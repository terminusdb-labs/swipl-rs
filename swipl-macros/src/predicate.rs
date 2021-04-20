use crate::kw;
use crate::util::*;

use proc_macro;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::parse::{Nothing, Parse, ParseStream, Result};
use syn::punctuated::Punctuated;
use syn::{parenthesized, parse_macro_input, Attribute, Block, Ident, LitStr, Token, Visibility};

pub fn predicates_macro(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let definitions = parse_macro_input!(stream as ForeignPredicateDefinitionBlock);

    let gen = definitions.generate();

    gen.into()
}

struct AttributedForeignPredicateDefinition {
    visibility: Visibility,
    predicate_name: Option<LitStr>,
    predicate_module: Option<LitStr>,
    _doc: Option<Attribute>,
    predicate: ForeignPredicateDefinition,
}

impl AttributedForeignPredicateDefinition {
    fn generate(&self) -> TokenStream {
        // what to generate?
        // - a function that returns an appropriate version of QueryResult for the specified determinism, with the given body
        // - an extern "C" trampoline, that calls this guy after converting its arguments and making a context
        // - a register function
        // - TODO a documented frontend for calling from rust as if this is a query
        let (def_name, def) = self.predicate.generate_definition();
        let (trampoline_name, trampoline) = self.predicate.generate_trampoline(&def_name);
        let registration = self.predicate.generate_registration(
            &trampoline_name,
            &self.visibility,
            self.predicate_name.as_ref(),
            self.predicate_module.as_ref(),
        );

        quote! {#def #trampoline #registration}
    }
}

impl Parse for AttributedForeignPredicateDefinition {
    fn parse(input: ParseStream) -> Result<Self> {
        let visibility = input.parse()?;
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

trait ForeignPredicateDefinitionImpl {
    fn generate_definition(&self) -> (Ident, TokenStream);
    fn generate_trampoline(&self, definition_name: &Ident) -> (Ident, TokenStream);
    fn generate_registration(
        &self,
        trampoline_name: &Ident,
        visibility: &Visibility,
        name: Option<&LitStr>,
        module: Option<&LitStr>,
    ) -> TokenStream;
    fn generate_frontend(&self) -> TokenStream;
}

enum ForeignPredicateDefinition {
    Det(DetForeignPredicateDefinition),
    Semidet(SemidetForeignPredicateDefinition),
}

impl ForeignPredicateDefinitionImpl for ForeignPredicateDefinition {
    fn generate_definition(&self) -> (Ident, TokenStream) {
        match self {
            Self::Det(d) => d.generate_definition(),
            Self::Semidet(d) => d.generate_definition(),
        }
    }

    fn generate_trampoline(&self, definition_name: &Ident) -> (Ident, TokenStream) {
        match self {
            Self::Det(d) => d.generate_trampoline(definition_name),
            Self::Semidet(d) => d.generate_trampoline(definition_name),
        }
    }

    fn generate_registration(
        &self,
        trampoline_name: &Ident,
        visibility: &Visibility,
        name: Option<&LitStr>,
        module: Option<&LitStr>,
    ) -> TokenStream {
        match self {
            Self::Det(d) => d.generate_registration(trampoline_name, visibility, name, module),
            Self::Semidet(d) => d.generate_registration(trampoline_name, visibility, name, module),
        }
    }

    fn generate_frontend(&self) -> TokenStream {
        todo!();
    }
}

impl Parse for ForeignPredicateDefinition {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(kw::det) {
            Ok(Self::Det(input.parse()?))
        } else if input.peek(kw::semidet) {
            Ok(Self::Semidet(input.parse()?))
        } else {
            Err(input.error("expected determinism specifier (det, semidet or nondet)"))
        }
    }
}

struct DetForeignPredicateDefinition {
    predicate_rust_name: Ident,
    params: Vec<Ident>,
    body: Block,
}

impl Parse for DetForeignPredicateDefinition {
    fn parse(input: ParseStream) -> Result<Self> {
        input.parse::<kw::det>()?;

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

        input.parse::<Token![->]>()?;
        input.parse::<kw::DetResult>()?;

        let body = input.parse()?;

        Ok(Self {
            predicate_rust_name: name,
            params,
            body,
        })
    }
}

impl ForeignPredicateDefinitionImpl for DetForeignPredicateDefinition {
    fn generate_definition(&self) -> (Ident, TokenStream) {
        let crt = crate_token();
        let definition_name = Ident::new(
            &format!("__{}_definition", self.predicate_rust_name),
            Span::call_site(),
        );
        let context_arg = &self.params[0];
        let term_args = self.params.iter().skip(1);
        let code = &self.body;
        (
            definition_name.clone(),
            quote! {
                fn #definition_name<'a, C: #crt::context::QueryableContextType>(#context_arg: &'a #crt::context::Context<'a, C>, #(#term_args : &#crt::term::Term<'a>),*) -> #crt::context::DetResult {
                    #code
                }
            },
        )
    }

    fn generate_trampoline(&self, definition_name: &Ident) -> (Ident, TokenStream) {
        let crt = crate_token();
        let trampoline_name = Ident::new(
            &format!("__{}_trampoline", self.predicate_rust_name),
            Span::call_site(),
        );
        let known_arity = self.params.len() - 1;
        let term_args = (0..known_arity).map(|i| quote! {&terms[#i]});
        (
            trampoline_name.clone(),
            quote! {
                unsafe extern "C" fn #trampoline_name(
                    term: #crt::sys::term_t,
                    arity: std::os::raw::c_int,
                    _control: *mut std::os::raw::c_void
                ) -> isize {
                    if #known_arity as usize != arity as usize {
                        // TODO actually throw an error
                        return 0;
                    }

                    let context = #crt::context::unmanaged_engine_context();
                    let mut terms: [std::mem::MaybeUninit<#crt::term::Term>;#known_arity] =
                        std::mem::MaybeUninit::uninit().assume_init();

                    for i in 0..#known_arity {
                        let term_ref = context.wrap_term_ref(term+i);
                        terms[i] = std::mem::MaybeUninit::new(term_ref);
                    }

                    let terms: [#crt::term::Term;#known_arity] = std::mem::transmute(terms);

                    let result = #definition_name(&context,
                                                  #(#term_args),*);

                    match result {
                        Ok(_) => 1,
                        // TODO actually error correctly
                        Err(_) => -1
                    }
                }
            },
        )
    }

    fn generate_registration(
        &self,
        trampoline_name: &Ident,
        visibility: &Visibility,
        name: Option<&LitStr>,
        module: Option<&LitStr>,
    ) -> TokenStream {
        let crt = crate_token();
        let registration_name = Ident::new(
            &format!("register_{}", self.predicate_rust_name),
            Span::call_site(),
        );
        let module_lit = match module {
            None => quote! {None},
            Some(m) => quote! {Some(#m)},
        };
        let rust_name = format!("{}", self.predicate_rust_name);
        let name_lit = match name {
            None => quote! {#rust_name},
            Some(n) => quote! {#n},
        };
        let arity = self.params.len() - 1;

        quote! {
            #visibility fn #registration_name() -> bool {
                // unsafe justification: register_foreign_in_module is unsafe due to the possibility that someone registers a function that is not actually expecting to handle a prolog call, and is not set up right for it. But we're generating this code ourselves, so we should have taken care of all preconditions.
                unsafe {
                    #crt::engine::register_foreign_in_module(
                        #module_lit,
                        #name_lit,
                        std::convert::TryInto::<u16>::try_into(#arity).expect("arity does not fit in an u16"),
                        true, // deterministic
                        None, // TODO actually figure out this meta thing
                        #trampoline_name
                    )
                }
            }
        }
    }

    fn generate_frontend(&self) -> TokenStream {
        todo!();
    }
}

struct SemidetForeignPredicateDefinition {
    predicate_rust_name: Ident,
    params: Vec<Ident>,
    body: Block,
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
        input.parse::<Token![->]>()?;
        input.parse::<kw::SemidetResult>()?;

        let body = input.parse()?;

        Ok(Self {
            predicate_rust_name: name,
            params,
            body,
        })
    }
}

impl ForeignPredicateDefinitionImpl for SemidetForeignPredicateDefinition {
    fn generate_definition(&self) -> (Ident, TokenStream) {
        let crt = crate_token();
        let definition_name = Ident::new(
            &format!("__{}_definition", self.predicate_rust_name),
            Span::call_site(),
        );
        let context_arg = &self.params[0];
        let term_args = self.params.iter().skip(1);
        let code = &self.body;
        (
            definition_name.clone(),
            quote! {
                fn #definition_name<'a, C: #crt::context::QueryableContextType>(#context_arg: &'a #crt::context::Context<'a, C>, #(#term_args : &#crt::term::Term<'a>),*) -> #crt::context::SemidetResult {
                    #code
                }
            },
        )
    }

    fn generate_trampoline(&self, definition_name: &Ident) -> (Ident, TokenStream) {
        let crt = crate_token();
        let trampoline_name = Ident::new(
            &format!("__{}_trampoline", self.predicate_rust_name),
            Span::call_site(),
        );
        let known_arity = self.params.len() - 1;
        let term_args = (0..known_arity).map(|i| quote! {&terms[#i]});
        (
            trampoline_name.clone(),
            quote! {
                unsafe extern "C" fn #trampoline_name(
                    term: #crt::sys::term_t,
                    arity: std::os::raw::c_int,
                    _control: *mut std::os::raw::c_void
                ) -> isize {
                    if #known_arity as usize != arity as usize {
                        // TODO actually throw an error
                        return 0;
                    }

                    let context = #crt::context::unmanaged_engine_context();
                    let mut terms: [std::mem::MaybeUninit<#crt::term::Term>;#known_arity] =
                        std::mem::MaybeUninit::uninit().assume_init();

                    for i in 0..#known_arity {
                        let term_ref = context.wrap_term_ref(term+i);
                        terms[i] = std::mem::MaybeUninit::new(term_ref);
                    }

                    let terms: [#crt::term::Term;#known_arity] = std::mem::transmute(terms);

                    let result = #definition_name(&context,
                                                  #(#term_args),*);

                    match result {
                        Ok(false) => 0,
                        Ok(true) => 1,
                        // TODO actually error correctly
                        Err(_) => -1
                    }
                }
            },
        )
    }

    fn generate_registration(
        &self,
        trampoline_name: &Ident,
        visibility: &Visibility,
        name: Option<&LitStr>,
        module: Option<&LitStr>,
    ) -> TokenStream {
        let crt = crate_token();
        let registration_name = Ident::new(
            &format!("register_{}", self.predicate_rust_name),
            Span::call_site(),
        );
        let module_lit = match module {
            None => quote! {None},
            Some(m) => quote! {Some(#m)},
        };
        let rust_name = format!("{}", self.predicate_rust_name);
        let name_lit = match name {
            None => quote! {#rust_name},
            Some(n) => quote! {#n},
        };
        let arity = self.params.len() - 1;

        quote! {
            #visibility fn #registration_name() -> bool {
                // unsafe justification: register_foreign_in_module is unsafe due to the possibility that someone registers a function that is not actually expecting to handle a prolog call, and is not set up right for it. But we're generating this code ourselves, so we should have taken care of all preconditions.
                unsafe {
                    #crt::engine::register_foreign_in_module(
                        #module_lit,
                        #name_lit,
                        std::convert::TryInto::<u16>::try_into(#arity).expect("arity does not fit in an u16"),
                        true, // deterministic
                        None, // TODO actually figure out this meta thing
                        #trampoline_name
                    )
                }
            }
        }
    }

    fn generate_frontend(&self) -> TokenStream {
        todo!();
    }
}

struct ForeignPredicateDefinitionBlock {
    definitions: Vec<AttributedForeignPredicateDefinition>,
}

impl Parse for ForeignPredicateDefinitionBlock {
    fn parse(input: ParseStream) -> Result<Self> {
        let punct: Punctuated<AttributedForeignPredicateDefinition, Nothing> =
            input.parse_terminated(AttributedForeignPredicateDefinition::parse)?;
        let definitions = punct.into_iter().collect();
        Ok(Self { definitions })
    }
}

impl ForeignPredicateDefinitionBlock {
    fn generate(&self) -> TokenStream {
        let code = self
            .definitions
            .iter()
            .map(|definition| definition.generate());
        quote! {#(#code)*}
    }
}
