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
            static pred: #crt::callable::LazyCallablePredicate<#arity> = #crt::callable::LazyCallablePredicate::new(Some(#module_lit), #name_lit);

            pred.as_callable()
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
