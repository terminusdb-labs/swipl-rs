use proc_macro2::Span;
use quote::quote;
use syn::parse::{Parse, ParseBuffer, Result};
use syn::{parse_macro_input, Ident, LitStr};

use crate::util::*;

pub fn atom_macro(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let atom = parse_macro_input!(stream as Atom);
    let atom_str = LitStr::new(&atom.0, atom.1);
    let crt = crate_token();
    let result = quote! {
        { static atom: #crt::prelude::LazyAtom = #crt::prelude::LazyAtom::new(#atom_str);
          #crt::prelude::AsAtom::as_atom(&atom)
        }
    };
    result.into()
}

struct Atom(String, Span);

impl Parse for Atom {
    fn parse(input: &ParseBuffer) -> Result<Self> {
        if input.peek(Ident) {
            let x: Ident = input.parse()?;

            Ok(Atom(x.to_string(), x.span()))
        } else {
            let x: LitStr = input.parse()?;
            Ok(Atom(x.value(), x.span()))
        }
    }
}
