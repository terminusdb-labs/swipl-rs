mod kw;
mod util;

mod blob;
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

#[proc_macro_attribute]
pub fn arc_blob(attr: TokenStream, item: TokenStream) -> TokenStream {
    blob::arc_blob_macro(attr, item)
}

#[proc_macro_attribute]
pub fn wrapped_arc_blob(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
