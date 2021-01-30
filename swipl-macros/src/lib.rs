use proc_macro::TokenStream;
use proc_macro2::{self, Span};
use proc_macro_crate::crate_name;
use quote::quote;
use syn::parse::{Parse, ParseStream, Result};
use syn::punctuated::Punctuated;
use syn::{parenthesized, parse_macro_input, Attribute, Ident, LitStr, Token};

struct PrologPredicate {
    predicate_rust_name: Ident,
    predicate_name: Option<LitStr>,
    predicate_module: Option<LitStr>,
    doc: Option<Attribute>,
    params: Vec<Ident>,
}

impl Parse for PrologPredicate {
    fn parse(input: ParseStream) -> Result<Self> {
        let attrs: Vec<Attribute> = input.call(Attribute::parse_outer)?;
        let mut doc = None;
        let mut predicate_name = None;
        let mut predicate_module = None;
        for attr in attrs {
            if attr.path.is_ident("doc") {
                doc = Some(attr);
            } else if attr.path.is_ident("name") {
                predicate_name = Some(attr.parse_args()?);
            } else if attr.path.is_ident("module") {
                predicate_module = Some(attr.parse_args()?);
            }
        }
        input.parse::<Token![fn]>()?;
        let name: Ident = input.parse()?;
        let params_stream;
        parenthesized!(params_stream in input);
        let params_punct: Punctuated<Ident, Token![,]> =
            params_stream.parse_terminated(Ident::parse)?;
        let params: Vec<_> = params_punct.into_iter().collect();

        Ok(Self {
            predicate_rust_name: name,
            predicate_name,
            predicate_module,
            doc,
            params,
        })
    }
}

impl PrologPredicate {
    fn into_definition(self) -> proc_macro2::TokenStream {
        // look up the swipl crate. if it doesn't exist, assume we are actually the swipl crate itself and we can use the special 'crate' namespace.
        let crt = match crate_name("swipl") {
            Ok(name) => {
                let name_ident = Ident::new(&name, Span::call_site());
                quote! {#name_ident}
            }
            Err(_) => quote! {crate},
        };
        let pred_static_ident = Ident::new(
            &format!("__{}_pred_ptr", self.predicate_rust_name),
            Span::call_site(),
        );
        let rust_name = self.predicate_rust_name;
        let params = self.params;
        let params_len = params.len();
        let doc = self.doc;
        let predicate_name = match self.predicate_name {
            Some(name) => name.value(),
            None => rust_name.to_string(),
        };
        let predicate_module = match self.predicate_module {
            Some(module) => module.value(),
            None => "user".to_string(),
        };
        let gen = quote! {
            static #pred_static_ident: std::sync::atomic::AtomicPtr<std::ffi::c_void> = std::sync::atomic::AtomicPtr::new(std::ptr::null_mut());

            #doc
            fn #rust_name<'a, T:#crt::context::QueryableContextType>(swipl_context: &'a #crt::context::Context<'a, T>, #(#params: &#crt::term::Term<'a>),*) -> #crt::context::Context<'a, #crt::context::Query> {
                swipl_context.assert_activated();
                let swipl_pred = #pred_static_ident.load(std::sync::atomic::Ordering::Relaxed);
                let swipl_predicate;
                if swipl_pred.is_null() {
                    // create that predicate
                    swipl_predicate = #crt::context::ActiveEnginePromise::new_predicate(
                        swipl_context,
                        &#crt::context::ActiveEnginePromise::new_functor(
                            swipl_context,
                            #predicate_name,
                            std::convert::TryInto::try_into(#params_len).expect("expected param len to fit inside a u16")),
                        &#crt::context::ActiveEnginePromise::new_module(
                            swipl_context,
                            #predicate_module));
                    // and store it in the static
                    #pred_static_ident.store(swipl_predicate.predicate_ptr(), std::sync::atomic::Ordering::Relaxed);
                }
                else {
                    swipl_predicate = unsafe {#crt::predicate::Predicate::wrap(swipl_pred)};
                }
                let swipl_call_args:Vec<&#crt::term::Term<'a>> = vec![#(#params),*];

                // TODO figure out what to do with that context module
                swipl_context.open_query(None, &swipl_predicate, &swipl_call_args)
            }
        };

        gen
    }
}

struct PrologPredicateBlock {
    predicates: Vec<PrologPredicate>,
}

impl Parse for PrologPredicateBlock {
    fn parse(input: ParseStream) -> Result<Self> {
        let punct: Punctuated<PrologPredicate, Token![;]> =
            input.parse_terminated(PrologPredicate::parse)?;
        let predicates = punct.into_iter().collect();
        Ok(Self { predicates })
    }
}

#[proc_macro]
pub fn prolog(item: TokenStream) -> TokenStream {
    let predicates = parse_macro_input!(item as PrologPredicateBlock);
    let definitions = predicates
        .predicates
        .into_iter()
        .map(|p| p.into_definition());
    let gen = quote! {#(#definitions)*};
    let result = gen.into();
    result
}
