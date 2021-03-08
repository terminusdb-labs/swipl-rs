mod kw;
mod util;

mod predicate;
mod prolog;
mod term;

use proc_macro::TokenStream;

#[proc_macro]
pub fn prolog(stream: TokenStream) -> TokenStream {
    prolog::prolog_macro(stream).into()
}

#[proc_macro]
pub fn predicates(stream: TokenStream) -> TokenStream {
    predicate::predicates_macro(stream).into()
}

#[proc_macro]
pub fn term(stream: TokenStream) -> TokenStream {
    term::term_macro(stream).into()
}
