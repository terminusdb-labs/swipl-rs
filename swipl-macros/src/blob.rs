use crate::util::*;

use proc_macro;
use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use syn::parse::{Parse, ParseStream, Result};
use syn::{parse_macro_input, Ident, Item, ItemEnum, ItemStruct, LitByteStr, LitStr};

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
    };

    result.into()
}

struct ArcBlobAttr {
    name: LitStr,
}

impl Parse for ArcBlobAttr {
    fn parse(input: ParseStream) -> Result<Self> {
        let name = input.parse()?;

        Ok(Self { name })
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
