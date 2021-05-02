use proc_macro;
use proc_macro2::Span;
use quote::quote;
use syn::parse::{Parse, ParseBuffer, Result};
use syn::{parse_macro_input, Ident, LitInt, LitStr, Token};

use crate::util::*;

pub fn pred_macro(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let definition = parse_macro_input!(stream as Pred);
    let arity = definition.arity;

    let name_lit = LitStr::new(&definition.name.to_string(), definition.name.span());
    let module_lit = match definition.module {
        Some(m) => LitStr::new(&m.to_string(), m.span()),
        None => LitStr::new("", Span::call_site()),
    };

    let crt = crate_token();
    let result = quote! {
        {
            static pred: std::sync::atomic::AtomicPtr<std::os::raw::c_void> = std::sync::atomic::AtomicPtr::new(std::ptr::null_mut());
            let mut loaded = pred.load(std::sync::atomic::Ordering::Relaxed);
            if loaded.is_null()  {
                // it really doesn't matter what engine this comes
                // from, as predicates are process wide and live
                // forever.
                let context = unsafe { #crt::context::unmanaged_engine_context() };
                let functor = context.new_functor(#name_lit, #arity);
                let module = context.new_module(#module_lit);
                loaded = context.new_predicate(&functor, &module).predicate_ptr();

                pred.store(loaded, std::sync::atomic::Ordering::Relaxed);
            }

            unsafe { #crt::callable::CallablePredicate::<#arity>::wrap(loaded) }
        }
    };

    result.into()
}

struct Pred {
    module: Option<Ident>,
    name: Ident,
    arity: LitInt,
}

impl Parse for Pred {
    fn parse(input: &ParseBuffer) -> Result<Self> {
        let mut module = None;
        if input.peek(Ident) && input.peek2(Token![:]) {
            module = Some(input.parse()?);
            input.parse::<Token![:]>()?;
        }

        let name = input.parse()?;
        input.parse::<Token![/]>()?;
        let arity = input.parse()?;

        Ok(Self {
            module,
            name,
            arity,
        })
    }
}
