use crate::kw;

use syn::parse::{Nothing, Parse, ParseStream, Result};
use syn::punctuated::Punctuated;
use syn::{
    braced, parenthesized, Attribute, Block, Ident, LitStr, Token, Visibility,
};

pub struct AttributedForeignPredicateDefinition {
    pub visibility: Visibility,
    pub predicate_name: Option<LitStr>,
    pub predicate_module: Option<LitStr>,
    pub _doc: Option<Attribute>,
    pub predicate: ForeignPredicateDefinition,
}

impl Parse for AttributedForeignPredicateDefinition {
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
        let predicate = input.parse()?;

        Ok(Self {
            visibility,
            predicate_name,
            predicate_module,
            _doc: doc,
            predicate,
        })
    }
}

pub enum ForeignPredicateDefinition {
    Semidet(SemidetForeignPredicateDefinition),
    Nondet(NondetForeignPredicateDefinition),
}

impl ForeignPredicateDefinition {
    pub fn rust_name(&self) -> &Ident {
        match self {
            Self::Semidet(s) => &s.predicate_rust_name,
            Self::Nondet(n) => &n.predicate_rust_name
        }
    }
}

impl Parse for ForeignPredicateDefinition {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(kw::semidet) {
            Ok(Self::Semidet(input.parse()?))
        } else if input.peek(kw::nondet) {
            Ok(Self::Nondet(input.parse()?))
        } else {
            Err(input.error("expected determinism specifier (det, semidet or nondet)"))
        }
    }
}

pub struct SemidetForeignPredicateDefinition {
    pub predicate_rust_name: Ident,
    pub params: Vec<Ident>,
    pub body: Block,
}

impl Parse for SemidetForeignPredicateDefinition {
    fn parse(input: ParseStream) -> Result<Self> {
        input.parse::<kw::semidet>()?;

        input.parse::<Token![fn]>()?;
        let name: Ident = input.parse()?;
        let params_stream;
        parenthesized!(params_stream in input);
        let params_punct: Punctuated<Ident, Token![,]> =
            params_stream.parse_terminated(Ident::parse)?;
        let span = params_stream.span();
        let params: Vec<_> = params_punct.into_iter().collect();
        if params.len() == 0 {
            return Err(syn::Error::new(
                span,
                "need at least one argument for query context",
            ));
        }

        let body = input.parse()?;

        Ok(Self {
            predicate_rust_name: name,
            params,
            body,
        })
    }
}

pub struct NondetForeignPredicateDefinition {
    pub predicate_rust_name: Ident,
    pub params: Vec<Ident>,
    pub data_name: Ident,
    pub data_type: syn::Path,
    pub setup_body: Block,
    pub call_body: Block,
}

impl Parse for NondetForeignPredicateDefinition {
    fn parse(input: ParseStream) -> Result<Self> {
        input.parse::<kw::nondet>()?;

        input.parse::<Token![fn]>()?;
        let name: Ident = input.parse()?;

        input.parse::<syn::token::Lt>()?;
        let data_type = input.parse::<syn::Path>()?;
        input.parse::<syn::token::Gt>()?;

        let params_stream;
        parenthesized!(params_stream in input);

        let params_punct: Punctuated<Ident, Token![,]> =
            params_stream.parse_terminated(Ident::parse)?;
        let span = params_stream.span();
        let params: Vec<_> = params_punct.into_iter().collect();
        if params.len() == 0 {
            return Err(syn::Error::new(
                span,
                "need at least one argument for query context",
            ));
        }

        let blocks;
        braced!(blocks in input);

        blocks.parse::<kw::setup>()?;
        blocks.parse::<Token![=>]>()?;
        let setup_body = blocks.parse()?;

        blocks.parse::<Token![,]>()?;

        blocks.parse::<kw::call>()?;
        let call_params_stream;
        parenthesized!(call_params_stream in blocks);
        let data_name = call_params_stream.parse::<Ident>()?;
        blocks.parse::<Token![=>]>()?;
        let call_body = blocks.parse()?;

        Ok(Self {
            predicate_rust_name: name,
            params,
            data_name,
            data_type,
            setup_body,
            call_body,
        })
    }
}

pub struct ForeignPredicateDefinitionBlock {
    pub definitions: Vec<AttributedForeignPredicateDefinition>,
}

impl Parse for ForeignPredicateDefinitionBlock {
    fn parse(input: ParseStream) -> Result<Self> {
        let punct: Punctuated<AttributedForeignPredicateDefinition, Nothing> =
            input.parse_terminated(AttributedForeignPredicateDefinition::parse)?;
        let definitions = punct.into_iter().collect();
        Ok(Self { definitions })
    }
}
