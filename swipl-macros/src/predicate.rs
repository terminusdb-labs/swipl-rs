use crate::kw;
use crate::util::*;

use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::parse::{Nothing, Parse, ParseStream, Result};
use syn::punctuated::Punctuated;
use syn::{
    braced, parenthesized, parse_macro_input, Attribute, Block, Ident, LitStr, Token, Visibility,
};

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
        let def = self.predicate.generate_definition();
        let (trampoline_name, trampoline) = self.predicate.generate_trampoline();
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
        let attrs: Vec<Attribute> = input.call(Attribute::parse_outer)?;
        let mut doc = None;
        let mut predicate_name = None;
        let mut predicate_module = None;
        for attr in attrs {
            if attr.path().is_ident("doc") {
                doc = Some(attr);
            } else if attr.path().is_ident("name") {
                predicate_name = Some(attr.parse_args()?);
            } else if attr.path().is_ident("module") {
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

trait ForeignPredicateDefinitionImpl {
    fn generate_definition(&self) -> TokenStream;
    fn generate_trampoline(&self) -> (Ident, TokenStream);
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
    Semidet(SemidetForeignPredicateDefinition),
    Nondet(NondetForeignPredicateDefinition),
}

impl ForeignPredicateDefinitionImpl for ForeignPredicateDefinition {
    fn generate_definition(&self) -> TokenStream {
        match self {
            Self::Semidet(d) => d.generate_definition(),
            Self::Nondet(d) => d.generate_definition(),
        }
    }

    fn generate_trampoline(&self) -> (Ident, TokenStream) {
        match self {
            Self::Semidet(d) => d.generate_trampoline(),
            Self::Nondet(d) => d.generate_trampoline(),
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
            Self::Semidet(d) => d.generate_registration(trampoline_name, visibility, name, module),
            Self::Nondet(d) => d.generate_registration(trampoline_name, visibility, name, module),
        }
    }

    fn generate_frontend(&self) -> TokenStream {
        todo!();
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
            Punctuated::parse_terminated(&params_stream)?;
        let span = params_stream.span();
        let params: Vec<_> = params_punct.into_iter().collect();
        if params.is_empty() {
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

fn semidet_definition_name<N: std::fmt::Display>(name: &N) -> Ident {
    Ident::new(&format!("{}", name), Span::call_site())
}

impl ForeignPredicateDefinitionImpl for SemidetForeignPredicateDefinition {
    fn generate_definition(&self) -> TokenStream {
        let crt = crate_token();
        let definition_name = semidet_definition_name(&self.predicate_rust_name);
        let context_arg = &self.params[0];
        let term_args = self.params.iter().skip(1);
        let code = &self.body;
        quote! {
            fn #definition_name<'a, C: #crt::context::QueryableContextType>(#context_arg: &'a #crt::context::Context<'a, C>, #(#term_args : &#crt::term::Term<'a>),*) -> #crt::result::PrologResult<()> {
                #code
            }
        }
    }

    fn generate_trampoline(&self) -> (Ident, TokenStream) {
        let crt = crate_token();
        let definition_name = semidet_definition_name(&self.predicate_rust_name);
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
                    term: #crt::fli::term_t,
                    arity: std::os::raw::c_int,
                    _control: #crt::fli::control_t
                ) -> isize {
                    let result = #crt::context::prolog_catch_unwind(|| {
                        if #known_arity as usize != arity as usize {
                            // TODO actually throw an error
                            return Err(#crt::result::PrologError::Failure);
                        }

                        let context = #crt::context::unmanaged_engine_context();
                        let mut terms: [std::mem::MaybeUninit<#crt::term::Term>;#known_arity] =
                            std::mem::MaybeUninit::uninit().assume_init();

                        #[allow(clippy::reversed_empty_ranges)]
                        for i in 0..#known_arity {
                            let term_ref = context.wrap_term_ref(term+i);
                            terms[i] = std::mem::MaybeUninit::new(term_ref);
                        }

                        let terms: [#crt::term::Term;#known_arity] = std::mem::transmute(terms);

                        #definition_name(&context,
                                         #(#term_args),*)
                    });

                    match result {
                        Ok(result) => match result {
                            Ok(()) => 1,
                            Err(_) => 0,
                        },
                        Err(_) => 0
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
        let registration_in_module_name = Ident::new(
            &format!("register_{}_in_module", self.predicate_rust_name),
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
            #visibility fn #registration_in_module_name(module: Option<&str>) -> bool {
                // unsafe justification: register_foreign_in_module is unsafe due to the possibility that someone registers a function that is not actually expecting to handle a prolog call, and is not set up right for it. But we're generating this code ourselves, so we should have taken care of all preconditions.
                unsafe {
                    #crt::init::register_foreign_in_module(
                        module,
                        #name_lit,
                        std::convert::TryInto::<u16>::try_into(#arity).expect("arity does not fit in an u16"),
                        true, // deterministic
                        None, // TODO actually figure out this meta thing
                        #trampoline_name
                    )
                }
            }

            #visibility fn #registration_name() -> bool {
                #registration_in_module_name(#module_lit)
            }
        }
    }

    fn generate_frontend(&self) -> TokenStream {
        todo!();
    }
}

struct NondetForeignPredicateDefinition {
    predicate_rust_name: Ident,
    params: Vec<Ident>,
    data_name: Ident,
    data_type: syn::Path,
    setup_body: Block,
    call_body: Block,
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
            Punctuated::parse_terminated(&params_stream)?;
        let span = params_stream.span();
        let params: Vec<_> = params_punct.into_iter().collect();
        if params.is_empty() {
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

fn nondet_definition_setup_name<N: std::fmt::Display>(name: &N) -> Ident {
    Ident::new(&format!("__{}_setup_definition", name), Span::call_site())
}

fn nondet_definition_call_name<N: std::fmt::Display>(name: &N) -> Ident {
    Ident::new(&format!("__{}_call_definition", name), Span::call_site())
}

impl ForeignPredicateDefinitionImpl for NondetForeignPredicateDefinition {
    fn generate_definition(&self) -> TokenStream {
        let crt = crate_token();
        let definition_setup_name = nondet_definition_setup_name(&self.predicate_rust_name);
        let definition_call_name = nondet_definition_call_name(&self.predicate_rust_name);
        let context_arg = &self.params[0];
        let term_args = self.params.iter().skip(1);
        let term_args_2 = term_args.clone();
        let setup_code = &self.setup_body;
        let call_code = &self.call_body;
        let data_name = &self.data_name;
        let data_type = &self.data_type;
        quote! {
            fn #definition_setup_name<'a, C: #crt::context::QueryableContextType>(#[allow(unused)] #context_arg: &'a #crt::context::Context<'a, C>, #(#[allow(unused)] #term_args : &#crt::term::Term<'a>),*) -> #crt::result::PrologResult<Option<#data_type>> {
                #setup_code
            }

            fn #definition_call_name<'a, C: #crt::context::QueryableContextType>(#data_name: &mut #data_type, #[allow(unused)] #context_arg: &'a #crt::context::Context<'a, C>, #(#[allow(unused)] #term_args_2 : &#crt::term::Term<'a>),*) -> #crt::result::PrologResult<bool> {
                #call_code
            }
        }
    }

    fn generate_trampoline(&self) -> (Ident, TokenStream) {
        let crt = crate_token();
        let trampoline_name = Ident::new(
            &format!("__{}_trampoline", self.predicate_rust_name),
            Span::call_site(),
        );
        let trampoline_type_check = Ident::new(
            &format!("__{}_trampoline_type_check", self.predicate_rust_name),
            Span::call_site(),
        );

        let definition_setup_name = nondet_definition_setup_name(&self.predicate_rust_name);
        let definition_call_name = nondet_definition_call_name(&self.predicate_rust_name);
        let data_type = &self.data_type;
        let known_arity = self.params.len() - 1;
        let term_args = (0..known_arity).map(|i| quote! {&terms[#i]});
        let term_args_2 = term_args.clone();
        (
            trampoline_name.clone(),
            quote! {
                fn #trampoline_type_check<T: Send+Unpin>() {}

                unsafe extern "C" fn #trampoline_name(
                    term: #crt::fli::term_t,
                    arity: std::os::raw::c_int,
                    control: #crt::fli::control_t
                ) -> isize {
                    // first, assert that the data type is send and unpin
                    #trampoline_type_check::<#data_type>();

                    let result = #crt::context::prolog_catch_unwind(|| {
                        if #known_arity as usize != arity as usize {
                            // TODO actually throw an error
                            return Err(#crt::result::PrologError::Failure);
                        }

                        let context = #crt::context::unmanaged_engine_context();
                        let mut terms: [std::mem::MaybeUninit<#crt::term::Term>;#known_arity] =
                            std::mem::MaybeUninit::uninit().assume_init();

                        #[allow(clippy::reversed_empty_ranges)]
                        for i in 0..#known_arity {
                            let term_ref = context.wrap_term_ref(term+i);
                            terms[i] = std::mem::MaybeUninit::new(term_ref);
                        }

                        let terms: [#crt::term::Term;#known_arity] = std::mem::transmute(terms);
                        let mut data: Box<#data_type>;
                        match #crt::fli::PL_foreign_control(control) {
                            0 => {
                                // this is the first call
                                let result = #definition_setup_name(&context,
                                                               #(#term_args),*)?;
                                if let Some(result) = result {
                                    // proceed
                                    data = Box::new(result);
                                }
                                else {
                                    // we're done
                                    return Ok(None);
                                }

                            },
                            2 => {
                                // this is a subsequent call - there should already be data.
                                let ptr = #crt::fli::PL_foreign_context_address(control) as *mut #data_type;
                                data = Box::from_raw(ptr);
                            },
                            1 => {
                                // this is a prune - we're not gonna continue executing this predicate
                                let ptr = #crt::fli::PL_foreign_context_address(control) as *mut #data_type;
                                data = Box::from_raw(ptr);
                                std::mem::drop(data);
                                return Ok(None);
                            },
                            n => panic!("unknown foreign control type {}", n)
                        }

                        // now data has been set up for us. lets call.
                        let result = #definition_call_name(&mut *data,
                                                           &context,
                                                           #(#term_args_2),*)?;

                        // if we get a true out of the call, that means more results are to follow. We need to remember the data in the control.
                        let retry;
                        match result {
                            true => {
                                // more results to follow
                                retry = Some(#crt::fli::_PL_retry_address(Box::into_raw(data) as *mut std::os::raw::c_void));
                            },
                            false => {
                                retry = None;
                            }
                        }

                        Ok(retry)
                    });

                    match result {
                        Ok(result) => match result {
                            Ok(None) => 1,
                            Ok(Some(r)) => r as isize,
                            Err(_) => 0,
                        },
                        Err(_) => 0
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
        let registration_in_module_name = Ident::new(
            &format!("register_{}_in_module", self.predicate_rust_name),
            Span::call_site(),
        );
        let rust_name = format!("{}", self.predicate_rust_name);
        let name_lit = match name {
            None => quote! {#rust_name},
            Some(n) => quote! {#n},
        };
        let arity = self.params.len() - 1;

        quote! {
            #visibility fn #registration_in_module_name(module: Option<&str>) -> bool {
                // unsafe justification: register_foreign_in_module is unsafe due to the possibility that someone registers a function that is not actually expecting to handle a prolog call, and is not set up right for it. But we're generating this code ourselves, so we should have taken care of all preconditions.
                unsafe {
                    #crt::init::register_foreign_in_module(
                        module,
                        #name_lit,
                        std::convert::TryInto::<u16>::try_into(#arity).expect("arity does not fit in an u16"),
                        false, // deterministic
                        None, // TODO actually figure out this meta thing
                        #trampoline_name
                    )
                }
            }

            #visibility fn #registration_name() -> bool {
                #registration_in_module_name(#module_lit)
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
            Punctuated::parse_terminated(&input)?;
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
