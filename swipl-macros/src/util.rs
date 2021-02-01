use proc_macro2::{Span, TokenStream};
use proc_macro_crate::crate_name;
use quote::quote;
use syn::Ident;

pub fn crate_token() -> TokenStream {
    match crate_name("swipl") {
        Ok(name) => {
            let name_ident = Ident::new(&name, Span::call_site());
            quote! {#name_ident}
        }
        Err(_) => quote! {crate},
    }
}
