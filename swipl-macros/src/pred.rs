use proc_macro2::Span;
use quote::quote;
use syn::parse::{Parse, ParseBuffer, Result};
use syn::{parse_macro_input, Ident, LitStr, Token};

use super::functor::Functor;
use crate::util::*;

pub fn pred_macro(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let definition = parse_macro_input!(stream as Pred);
    let arity = definition.arity as usize;

    let name_lit = LitStr::new(&definition.name, definition.name_span);
    let module_lit = match definition.module {
        Some(m) => LitStr::new(&m.0, m.1),
        None => LitStr::new("", Span::call_site()),
    };

    let crt = crate_token();
    let result = quote! {
        {
            static PRED: #crt::callable::LazyCallablePredicate<#arity> = #crt::callable::LazyCallablePredicate::new(Some(#module_lit), #name_lit);

            PRED.as_callable()
        }
    };

    result.into()
}

struct Pred {
    module: Option<(String, Span)>,
    name: String,
    name_span: Span,
    arity: u16,
}

impl Parse for Pred {
    fn parse(input: &ParseBuffer) -> Result<Self> {
        let mut module: Option<(String, Span)> = None;
        if input.peek2(Token![:]) {
            // we start with a module declaration
            if input.peek(LitStr) {
                let m: LitStr = input.parse()?;
                module = Some((m.value(), m.span()));
            } else if input.peek(Ident) {
                let m: Ident = input.parse()?;
                module = Some((m.to_string(), m.span()));
            } else {
                return Err(syn::parse::Error::new(
                    input.span(),
                    "Invalid module declaration",
                ));
            }

            input.parse::<Token![:]>()?;
        } else if input.peek(LitStr) && !input.peek2(Token![,]) && !input.peek2(Token![/]) {
            // This is the special case where we just have a single string that needs parsing.
            let x: LitStr = input.parse()?;
            let s = x.value();
            if let Some(pos) = s.rfind('/') {
                let module_and_name = &s[..pos];
                let arity_s = &s[pos + 1..];

                let arity: u16;
                if let Ok(a) = arity_s.parse::<u16>() {
                    arity = a;
                } else {
                    return Err(syn::parse::Error::new(
                        x.span(),
                        format!("\"{}\" is not a valid arity", arity_s),
                    ));
                }

                let module: Option<String>;
                let name: String;
                if let Some(pos) = module_and_name.rfind(':') {
                    module = Some(module_and_name[..pos].to_string());
                    name = module_and_name[pos + 1..].to_string();
                } else {
                    module = None;
                    name = module_and_name.to_string();
                }

                if name.is_empty() {
                    return Err(syn::parse::Error::new(x.span(), "invalid predicate name"));
                }

                return Ok(Self {
                    module: module.map(|m| (m, x.span())),
                    name,
                    name_span: x.span(),
                    arity,
                });
            } else {
                return Err(syn::parse::Error::new(
                    x.span(),
                    "expected predicate format [module:]<name>/<arity> but no '/' found",
                ));
            }
        }

        // equivalent to functor parsing
        let functor = Functor::parse(input)?;
        Ok(Self {
            module,
            name: functor.name,
            name_span: functor.name_span,
            arity: functor.arity,
        })
    }
}
