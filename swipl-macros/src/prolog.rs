use crate::util::*;
use proc_macro;
use proc_macro2::{self, Span, TokenStream};
use quote::quote;
use syn::parse::{Parse, ParseStream, Result};
use syn::punctuated::Punctuated;
use syn::{parenthesized, parse_macro_input, Attribute, Ident, LitStr, Token, Visibility};

pub fn prolog_macro(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let predicates = parse_macro_input!(stream as PrologPredicateBlock);
    let definitions = predicates
        .predicates
        .into_iter()
        .map(|p| p.into_definition());
    let gen = quote! {#(#definitions)*};
    let result = gen.into();
    result
}

struct PrologPredicate {
    predicate_rust_name: Ident,
    predicate_name: Option<LitStr>,
    predicate_module: Option<LitStr>,
    doc: Option<Attribute>,
    visibility: Visibility,
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
        let visibility = input.parse()?;
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
            visibility,
            params,
        })
    }
}

impl PrologPredicate {
    fn into_definition(self) -> TokenStream {
        // look up the swipl crate. if it doesn't exist, assume we are actually the swipl crate itself and we can use the special 'crate' namespace.
        let crt = crate_token();
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
        let visibility = self.visibility;
        let gen = quote! {
            static #pred_static_ident: #crt::callable::LazyCallablePredicate<#params_len> = #crt::callable::LazyCallablePredicate::new(Some(#predicate_module), #predicate_name);

            #doc
            #visibility fn #rust_name<'a, T:#crt::context::QueryableContextType>(swipl_context: &'a #crt::context::Context<'a, T>, #(#params: &#crt::term::Term<'a>),*) -> #crt::context::Context<'a, impl #crt::callable::OpenCall> {
                swipl_context.assert_activated();
                let swipl_call_args = [#(#params),*];


                // TODO figure out what to do with that context module
                swipl_context.open(#pred_static_ident.as_callable(), swipl_call_args)
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
