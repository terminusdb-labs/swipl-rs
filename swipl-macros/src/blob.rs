use crate::kw;
use crate::util::*;

use proc_macro;
use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use syn::parse::{Parse, ParseStream, Result};
use syn::{
    parse_macro_input, Ident, Item, ItemEnum, ItemStruct, LitByteStr, LitStr, Path, Token,
    Visibility,
};

pub fn arc_blob_macro(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let crt = crate_token();
    let attr_def = parse_macro_input!(attr as ArcBlobAttr);

    let name_lit = attr_def.name;
    let name = name_lit.value();
    let mut name_bytes = Vec::with_capacity(name.as_bytes().len() + 1);
    name_bytes.extend_from_slice(name.as_bytes());
    name_bytes.push(0);
    let name_bytes_lit = LitByteStr::new(&name_bytes, Span::call_site());

    let item_def = parse_macro_input!(item as ArcBlobItem);
    let item_name = item_def.name_ident();

    let blob_definition_ident = Ident::new(
        &format!("__{}_blob_definition", item_name),
        Span::call_site(),
    );

    let blob_acquire = Ident::new(&format!("__{}_blob_acquire", item_name), Span::call_site());
    let blob_release = Ident::new(&format!("__{}_blob_release", item_name), Span::call_site());
    let blob_compare = Ident::new(&format!("__{}_blob_compare", item_name), Span::call_site());
    let blob_write = Ident::new(&format!("__{}_blob_write", item_name), Span::call_site());

    let default_implementation;
    if attr_def.defaults {
        default_implementation = quote! {
            impl #crt::blob::ArcBlobImpl for #item_name {}
        };
    } else {
        default_implementation = quote! {};
    }

    let result = quote! {
        #item_def

        impl ArcBlobInfo for #item_name {
            fn blob_name() -> &'static str {
                #name_lit
            }
        }

        static #blob_definition_ident: std::sync::atomic::AtomicPtr<#crt::fli::PL_blob_t> = std::sync::atomic::AtomicPtr::new(std::ptr::null_mut());

        unsafe extern "C" fn #blob_acquire(a: #crt::fli::atom_t) {
            #crt::blob::acquire_arc_blob::<#item_name>(a);
        }

        unsafe extern "C" fn #blob_release(a: #crt::fli::atom_t) -> std::os::raw::c_int {
            #crt::blob::release_arc_blob::<#item_name>(a);

            1
        }

        unsafe extern "C" fn #blob_compare(a: #crt::fli::atom_t, b: #crt::fli::atom_t)->std::os::raw::c_int {
            let a_val = #crt::fli::PL_blob_data(a,
                                                std::ptr::null_mut(),
                                                std::ptr::null_mut())
                as *const #item_name;
            let b_val = #crt::fli::PL_blob_data(b,
                                                std::ptr::null_mut(),
                                                std::ptr::null_mut())
                as *const #item_name;
            match #crt::blob::ArcBlobImpl::compare(&*a_val, &*b_val) {
                std::cmp::Ordering::Less => -1,
                std::cmp::Ordering::Equal => 0,
                std::cmp::Ordering::Greater => 1
            }
        }

        unsafe extern "C" fn #blob_write(s: *mut #crt::fli::IOSTREAM,
                                         a: #crt::fli::atom_t,
                                         _flags: std::os::raw::c_int)
                                         -> std::os::raw::c_int {
            let a_val = #crt::fli::PL_blob_data(a,
                                                std::ptr::null_mut(),
                                                std::ptr::null_mut())
                as *const #item_name;
            let mut stream = #crt::stream::PrologStream::wrap(s);
            match #crt::blob::ArcBlobImpl::write(&*a_val, &mut stream) {
                Ok(_) => 1,
                Err(_) => 0
            }
        }

        unsafe impl #crt::blob::ArcBlob for #item_name {
            fn get_blob_definition() -> &'static #crt::fli::PL_blob_t {
                let mut definition = #blob_definition_ident.load(std::sync::atomic::Ordering::Relaxed);
                if definition.is_null() {
                    let new_definition = Box::new(#crt::blob::create_blob_definition(
                        #name_bytes_lit,
                        false,
                        true,
                        true,
                        Some(#blob_acquire),
                        Some(#blob_release),
                        Some(#blob_compare),
                        Some(#blob_write),
                        None,
                        None));

                    let new_definition_ptr = Box::into_raw(new_definition);
                    if #blob_definition_ident.compare_exchange(
                        std::ptr::null_mut(),
                        new_definition_ptr,
                        std::sync::atomic::Ordering::Relaxed,
                        std::sync::atomic::Ordering::Relaxed,
                    ).is_err() {
                        // swap failed, so someone beat us to creating the definition.
                        // We have to forget what we created.
                        std::mem::drop(unsafe { Box::from_raw(new_definition_ptr) });
                    }

                    definition = #blob_definition_ident.load(std::sync::atomic::Ordering::Relaxed);
                }

                unsafe { std::mem::transmute(definition) }
            }
        }

        #default_implementation
    };

    result.into()
}

pub fn wrapped_arc_blob_macro(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let crt = crate_token();

    let item_def = parse_macro_input!(item as WrappedArcBlobItem);
    let name_lit = item_def.name;
    let name = name_lit.value();
    let mut name_bytes = Vec::with_capacity(name.as_bytes().len() + 1);
    name_bytes.extend_from_slice(name.as_bytes());
    name_bytes.push(0);
    let name_bytes_lit = LitByteStr::new(&name_bytes, Span::call_site());

    let item_name = &item_def.wrap_type;
    let visibility = &item_def.visibility;
    let inner_type_name = &item_def.inner_type;

    let blob_definition_ident = Ident::new(
        &format!("__{}_blob_definition", item_name),
        Span::call_site(),
    );

    let blob_acquire = Ident::new(&format!("__{}_blob_acquire", item_name), Span::call_site());
    let blob_release = Ident::new(&format!("__{}_blob_release", item_name), Span::call_site());
    let blob_compare = Ident::new(&format!("__{}_blob_compare", item_name), Span::call_site());
    let blob_write = Ident::new(&format!("__{}_blob_write", item_name), Span::call_site());

    let default_implementation;
    if item_def.defaults {
        default_implementation = quote! {
            impl #crt::blob::WrappedArcBlobImpl for #item_name {}
        };
    } else {
        default_implementation = quote! {};
    }

    let result = quote! {
        #visibility struct #item_name(#visibility Arc<#inner_type_name>);

        impl std::ops::Deref for #item_name {
            type Target = #inner_type_name;

            fn deref(&self) -> &#inner_type_name {
                &self.0
            }
        }


        impl WrappedArcBlobInfo for #item_name {
            type Inner = #inner_type_name;

            fn blob_name() -> &'static str {
                #name_lit
            }

            fn get_arc(&self) -> &std::sync::Arc<#inner_type_name> {
                &self.0
            }

            fn from_arc(arc: std::sync::Arc<#inner_type_name>) -> Self {
                Self(arc)
            }
        }

        static #blob_definition_ident: std::sync::atomic::AtomicPtr<#crt::fli::PL_blob_t> = std::sync::atomic::AtomicPtr::new(std::ptr::null_mut());

        unsafe extern "C" fn #blob_acquire(a: #crt::fli::atom_t) {
            #crt::blob::acquire_arc_blob::<#item_name>(a);
        }

        unsafe extern "C" fn #blob_release(a: #crt::fli::atom_t) -> std::os::raw::c_int {
            #crt::blob::release_arc_blob::<#item_name>(a);

            1
        }

        unsafe extern "C" fn #blob_compare(a: #crt::fli::atom_t, b: #crt::fli::atom_t)->std::os::raw::c_int {
            let a_val = #crt::fli::PL_blob_data(a,
                                                std::ptr::null_mut(),
                                                std::ptr::null_mut())
                as *const #inner_type_name;
            let b_val = #crt::fli::PL_blob_data(b,
                                                std::ptr::null_mut(),
                                                std::ptr::null_mut())
                as *const #inner_type_name;
            match <#item_name as #crt::blob::WrappedArcBlobImpl>::compare(&*a_val, &*b_val) {
                std::cmp::Ordering::Less => -1,
                std::cmp::Ordering::Equal => 0,
                std::cmp::Ordering::Greater => 1
            }
        }

        unsafe extern "C" fn #blob_write(s: *mut #crt::fli::IOSTREAM,
                                         a: #crt::fli::atom_t,
                                         _flags: std::os::raw::c_int)
                                         -> std::os::raw::c_int {
            let a_val = #crt::fli::PL_blob_data(a,
                                                std::ptr::null_mut(),
                                                std::ptr::null_mut())
                as *const #inner_type_name;
            let mut stream = #crt::stream::PrologStream::wrap(s);
            match <#item_name as #crt::blob::WrappedArcBlobImpl>::write(&*a_val, &mut stream) {
                Ok(_) => 1,
                Err(_) => 0
            }
        }

        unsafe impl #crt::blob::WrappedArcBlob for #item_name {
            fn get_blob_definition() -> &'static #crt::fli::PL_blob_t {
                let mut definition = #blob_definition_ident.load(std::sync::atomic::Ordering::Relaxed);
                if definition.is_null() {
                    let new_definition = Box::new(#crt::blob::create_blob_definition(
                        #name_bytes_lit,
                        false,
                        true,
                        true,
                        Some(#blob_acquire),
                        Some(#blob_release),
                        Some(#blob_compare),
                        Some(#blob_write),
                        None,
                        None));

                    let new_definition_ptr = Box::into_raw(new_definition);
                    if #blob_definition_ident.compare_exchange(
                        std::ptr::null_mut(),
                        new_definition_ptr,
                        std::sync::atomic::Ordering::Relaxed,
                        std::sync::atomic::Ordering::Relaxed,
                    ).is_err() {
                        // swap failed, so someone beat us to creating the definition.
                        // We have to forget what we created.
                        std::mem::drop(unsafe { Box::from_raw(new_definition_ptr) });
                    }

                    definition = #blob_definition_ident.load(std::sync::atomic::Ordering::Relaxed);
                }

                unsafe { std::mem::transmute(definition) }
            }
        }

        unsafe impl #crt::term::Unifiable for #item_name {
            fn unify(&self, term: &#crt::term::Term) -> bool {
                let blob_definition = Self::get_blob_definition();
                unsafe { #crt::blob::unify_with_arc(term, blob_definition, &self.0) }
            }
        }

        unsafe impl #crt::term::TermGetable for #item_name {
            fn get(term: &#crt::term::Term) -> Option<Self> {
                let blob_definition = Self::get_blob_definition();
                let arc_opt = unsafe { #crt::blob::get_arc_from_term(term, blob_definition) };
                arc_opt.map(|a|Self(a))
            }
        }

        unsafe impl #crt::term::TermPutable for #item_name {
            fn put(&self, term: &#crt::term::Term) {
                let blob_definition = Self::get_blob_definition();
                unsafe { #crt::blob::put_arc_in_term(term, blob_definition, &self.0) }
            }
        }


        #default_implementation
    };

    result.into()
}

pub fn clone_blob_macro(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let crt = crate_token();
    let attr_def = parse_macro_input!(attr as ArcBlobAttr);

    let name_lit = attr_def.name;
    let name = name_lit.value();
    let mut name_bytes = Vec::with_capacity(name.as_bytes().len() + 1);
    name_bytes.extend_from_slice(name.as_bytes());
    name_bytes.push(0);
    let name_bytes_lit = LitByteStr::new(&name_bytes, Span::call_site());

    let item_def = parse_macro_input!(item as ArcBlobItem);
    let item_name = item_def.name_ident();

    let blob_definition_ident = Ident::new(
        &format!("__{}_blob_definition", item_name),
        Span::call_site(),
    );

    let blob_release = Ident::new(&format!("__{}_blob_release", item_name), Span::call_site());
    let blob_compare = Ident::new(&format!("__{}_blob_compare", item_name), Span::call_site());
    let blob_write = Ident::new(&format!("__{}_blob_write", item_name), Span::call_site());

    let default_implementation;
    if attr_def.defaults {
        default_implementation = quote! {
            impl #crt::blob::CloneBlobImpl for #item_name {}
        };
    } else {
        default_implementation = quote! {};
    }

    let result = quote! {
        #item_def

        impl CloneBlobInfo for #item_name {
            fn blob_name() -> &'static str {
                #name_lit
            }
        }

        static #blob_definition_ident: std::sync::atomic::AtomicPtr<#crt::fli::PL_blob_t> = std::sync::atomic::AtomicPtr::new(std::ptr::null_mut());

        unsafe extern "C" fn #blob_release(a: #crt::fli::atom_t) -> std::os::raw::c_int {
            #crt::blob::release_clone_blob::<#item_name>(a);

            1
        }

        unsafe extern "C" fn #blob_compare(a: #crt::fli::atom_t, b: #crt::fli::atom_t)->std::os::raw::c_int {
            let a_val = #crt::fli::PL_blob_data(a,
                                                std::ptr::null_mut(),
                                                std::ptr::null_mut())
                as *const #item_name;
            let b_val = #crt::fli::PL_blob_data(b,
                                                std::ptr::null_mut(),
                                                std::ptr::null_mut())
                as *const #item_name;
            match #crt::blob::CloneBlobImpl::compare(&*a_val, &*b_val) {
                std::cmp::Ordering::Less => -1,
                std::cmp::Ordering::Equal => 0,
                std::cmp::Ordering::Greater => 1
            }
        }

        unsafe extern "C" fn #blob_write(s: *mut #crt::fli::IOSTREAM,
                                         a: #crt::fli::atom_t,
                                         _flags: std::os::raw::c_int)
                                         -> std::os::raw::c_int {
            let a_val = #crt::fli::PL_blob_data(a,
                                                std::ptr::null_mut(),
                                                std::ptr::null_mut())
                as *const #item_name;
            let mut stream = #crt::stream::PrologStream::wrap(s);
            match #crt::blob::CloneBlobImpl::write(&*a_val, &mut stream) {
                Ok(_) => 1,
                Err(_) => 0
            }
        }

        unsafe impl #crt::blob::CloneBlob for #item_name {
            fn get_blob_definition() -> &'static #crt::fli::PL_blob_t {
                let mut definition = #blob_definition_ident.load(std::sync::atomic::Ordering::Relaxed);
                if definition.is_null() {
                    let new_definition = Box::new(#crt::blob::create_blob_definition(
                        #name_bytes_lit,
                        false,
                        false,
                        false,
                        None,
                        Some(#blob_release),
                        Some(#blob_compare),
                        Some(#blob_write),
                        None,
                        None));

                    let new_definition_ptr = Box::into_raw(new_definition);
                    if #blob_definition_ident.compare_exchange(
                        std::ptr::null_mut(),
                        new_definition_ptr,
                        std::sync::atomic::Ordering::Relaxed,
                        std::sync::atomic::Ordering::Relaxed,
                    ).is_err() {
                        // swap failed, so someone beat us to creating the definition.
                        // We have to forget what we created.
                        std::mem::drop(unsafe { Box::from_raw(new_definition_ptr) });
                    }

                    definition = #blob_definition_ident.load(std::sync::atomic::Ordering::Relaxed);
                }

                unsafe { std::mem::transmute(definition) }
            }
        }

        unsafe impl #crt::term::Unifiable for #item_name {
            fn unify(&self, term: &#crt::term::Term) -> bool {
                let blob_definition = Self::get_blob_definition();
                unsafe { #crt::blob::unify_with_cloneable(term, blob_definition, self) }
            }
        }

        unsafe impl #crt::term::TermGetable for #item_name {
            fn get(term: &#crt::term::Term) -> Option<Self> {
                let blob_definition = Self::get_blob_definition();
                let cloned_opt = unsafe { #crt::blob::get_cloned_from_term(term, blob_definition) };
                cloned_opt
            }
        }

        unsafe impl #crt::term::TermPutable for #item_name {
            fn put(&self, term: &#crt::term::Term) {
                let blob_definition = Self::get_blob_definition();
                unsafe { #crt::blob::put_cloneable_in_term(term, blob_definition, self) }
            }
        }

        #default_implementation
    };

    result.into()
}

pub fn wrapped_clone_blob_macro(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let item_def = parse_macro_input!(item as WrappedArcBlobItem);
    let name_lit = item_def.name;
    let item_name = &item_def.wrap_type;
    let visibility = &item_def.visibility;
    let inner_type_name = &item_def.inner_type;

    let attr;
    if item_def.defaults {
        attr = quote! {#[clone_blob(#name_lit, defaults)]};
    } else {
        attr = quote! {#[clone_blob(#name_lit)]};
    }

    let result = quote! {
        #attr
        #[derive(Clone)]
        #visibility struct #item_name(#visibility #inner_type_name);

        impl std::ops::Deref for #item_name {
            type Target = #inner_type_name;

            fn deref(&self) -> &#inner_type_name {
                &self.0
            }
        }
    };

    result.into()
}

struct ArcBlobAttr {
    name: LitStr,
    defaults: bool,
}

impl Parse for ArcBlobAttr {
    fn parse(input: ParseStream) -> Result<Self> {
        let name = input.parse()?;

        let defaults;
        if input.peek(Token![,]) {
            input.parse::<Token![,]>()?;
            input.parse::<kw::defaults>()?;
            defaults = true;
        } else {
            defaults = false;
        }

        Ok(Self { name, defaults })
    }
}

enum ArcBlobItem {
    Struct(ItemStruct),
    Enum(ItemEnum),
}

impl ArcBlobItem {
    fn name_ident(&self) -> &Ident {
        match self {
            Self::Struct(s) => &s.ident,
            Self::Enum(e) => &e.ident,
        }
    }
}

impl Parse for ArcBlobItem {
    fn parse(input: ParseStream) -> Result<Self> {
        let item: Item = input.parse()?;
        match item {
            Item::Struct(s) => Ok(Self::Struct(s)),
            Item::Enum(e) => Ok(Self::Enum(e)),
            _ => Err(syn::Error::new(
                Span::call_site(),
                "arc blob attributes are only supported with struct or enum",
            )),
        }
    }
}

impl ToTokens for ArcBlobItem {
    fn to_tokens(&self, stream: &mut TokenStream) {
        match self {
            Self::Struct(s) => s.to_tokens(stream),
            Self::Enum(e) => e.to_tokens(stream),
        }
    }
}

struct WrappedArcBlobItem {
    visibility: Visibility,
    name: LitStr,
    wrap_type: Ident,
    inner_type: Path,
    defaults: bool,
}
impl Parse for WrappedArcBlobItem {
    fn parse(input: ParseStream) -> Result<Self> {
        let name = input.parse()?;
        input.parse::<Token![,]>()?;
        let visibility = input.parse()?;
        let wrap_type = input.parse()?;
        input.parse::<Token![,]>()?;
        let inner_type = input.parse()?;

        let defaults;
        if input.peek(Token![,]) {
            input.parse::<Token![,]>()?;
            input.parse::<kw::defaults>()?;
            defaults = true;
        } else {
            defaults = false;
        }

        Ok(Self {
            visibility,
            name,
            wrap_type,
            inner_type,
            defaults,
        })
    }
}
