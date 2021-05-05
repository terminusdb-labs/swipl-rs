use proc_macro2::{Span, TokenStream};
use proc_macro_crate::crate_name;
use quote::quote;
use syn::Ident;

pub fn crate_token() -> TokenStream {
    let current_crate_name = std::env::var("CARGO_CRATE_NAME");
    if current_crate_name.is_ok() && current_crate_name.unwrap() == "swipl" {
        // check that this is either compiling swipl as the primary package, or that environment variables indicating a rustdoc binary compile is missing.
        if std::env::var("CARGO_PRIMARY_PACKAGE").is_ok() ||
            std::env::var("UNSTABLE_RUSTDOC_TEST_LINE").is_err() {
            quote!{crate}
        }
        else {
            // not the primary package but one of the tests. assume 'swipl'.
            quote!{swipl}
        }
    }
    else {
        match crate_name("swipl") {
            Ok(name) => {
                let name_ident = Ident::new(&name, Span::call_site());
                quote! {#name_ident}
            }
            Err(_) => {
                quote! {swipl}
            },
        }
    }
}
