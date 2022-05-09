use proc_macro;
use proc_macro2::Span;
use quote::quote;
use syn::parse::{Parse, ParseBuffer, Result};
use syn::{parse_macro_input, Ident, LitInt, LitStr, Token};

use crate::util::*;

pub fn functor_macro(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let functor = parse_macro_input!(stream as Functor);
    let functor_name_str = LitStr::new(&functor.name, functor.name_span);
    let functor_arity_int = LitInt::new(&functor.arity.to_string(), functor.arity_span);
    let crt = crate_token();
    let result = quote! {
        { static functor: #crt::prelude::LazyFunctor = #crt::prelude::LazyFunctor::new(#functor_name_str, #functor_arity_int);
          functor.as_functor()
        }
    };
    result.into()
}

struct Functor {
    name: String,
    name_span: Span,
    arity: u16,
    arity_span: Span,
}

impl Parse for Functor {
    fn parse(input: &ParseBuffer) -> Result<Self> {
        let name: String;
        let name_span: Span;
        if input.peek(LitStr) {
            // There is two possibilities.
            //
            // 1. This is a string of format "name/arity", which we'll
            // need to parse.
            // 2. This is a a string that is followed by a comma or
            // slash, and an arity.
            //
            // We will deal with 1 here and return early. Second part is equal for ident so we'll handle it in a common code path.
            let x: LitStr = input.parse()?;

            if input.is_empty() {
                // we need to parse
                let s = x.value();
                if let Some(pos) = s.rfind('/') {
                    let name = &s[..pos];
                    let arity_s = &s[pos + 1..];

                    if let Ok(arity) = arity_s.parse::<u16>() {
                        return Ok(Functor {
                            name: name.to_string(),
                            name_span: x.span(),
                            arity: arity,
                            arity_span: x.span(),
                        });
                    } else {
                        return Err(syn::parse::Error::new(
                            x.span(),
                            format!("\"{}\" is not a valid arity", arity_s),
                        ));
                    }
                } else {
                    return Err(syn::parse::Error::new(
                        x.span(),
                        "expected functor format <name>/<arity> but no '/' found",
                    ));
                }
            } else {
                name = x.value();
                name_span = x.span();
            }
        } else {
            let x: Ident = input.parse()?;

            name = x.to_string();
            name_span = x.span();
        }

        if input.peek(Token![,]) {
            input.parse::<Token![,]>()?;
        } else if input.peek(Token![/]) {
            input.parse::<Token![/]>()?;
        } else {
            return Err(syn::parse::Error::new(
                input.span(),
                "invalid functor separator",
            ));
        }

        let arity_token = input.parse::<LitInt>()?;
        let arity: u16 = arity_token.base10_parse()?;

        Ok(Self {
            name,
            name_span,
            arity,
            arity_span: arity_token.span(),
        })
    }
}
