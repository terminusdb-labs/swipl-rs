mod kw;
mod util;

mod blob;
mod pred;
mod predicate;
mod prolog;
mod term;

use proc_macro::TokenStream;

#[proc_macro]
pub fn prolog(stream: TokenStream) -> TokenStream {
    prolog::prolog_macro(stream).into()
}

#[proc_macro]
pub fn pred(stream: TokenStream) -> TokenStream {
    pred::pred_macro(stream).into()
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

#[proc_macro]
pub fn wrapped_arc_blob(item: TokenStream) -> TokenStream {
    blob::wrapped_arc_blob_macro(item)
}

#[proc_macro_attribute]
pub fn clone_blob(attr: TokenStream, item: TokenStream) -> TokenStream {
    blob::clone_blob_macro(attr, item)
}

#[proc_macro]
pub fn wrapped_clone_blob(item: TokenStream) -> TokenStream {
    blob::wrapped_clone_blob_macro(item)
}
