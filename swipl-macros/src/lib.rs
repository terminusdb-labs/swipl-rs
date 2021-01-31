mod predicate;
mod prolog;
mod util;

use proc_macro::TokenStream;

#[proc_macro]
pub fn prolog(stream: TokenStream) -> TokenStream {
    prolog::prolog_macro(stream.into()).into()
}

#[proc_macro]
pub fn predicates(stream: TokenStream) -> TokenStream {
    predicate::predicates_macro(stream.into()).into()
}
