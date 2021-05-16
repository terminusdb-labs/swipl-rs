use swipl_macros_parse::predicate::*;

use crate::util::*;

use proc_macro;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{
    parse_macro_input, Ident, LitStr, Visibility,
};

pub fn predicates_macro(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let definitions = parse_macro_input!(stream as ForeignPredicateDefinitionBlock);

    let gen = generate_definitions(&definitions);

    gen.into()
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

fn semidet_definition_name<N: std::fmt::Display>(name: &N) -> Ident {
    Ident::new(&format!("__{}_definition", name), Span::call_site())
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
                    _control: *mut std::os::raw::c_void
                ) -> isize {
                    let result = #crt::context::prolog_catch_unwind(|| {
                        if #known_arity as usize != arity as usize {
                            // TODO actually throw an error
                            return Err(#crt::result::PrologError::Failure);
                        }

                        let context = #crt::context::unmanaged_engine_context();
                        let mut terms: [std::mem::MaybeUninit<#crt::term::Term>;#known_arity] =
                            std::mem::MaybeUninit::uninit().assume_init();

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
                    #crt::init::register_foreign_in_module(
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
                    control: *mut std::os::raw::c_void
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
                    #crt::init::register_foreign_in_module(
                        #module_lit,
                        #name_lit,
                        std::convert::TryInto::<u16>::try_into(#arity).expect("arity does not fit in an u16"),
                        false, // deterministic
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

fn generate_definition(definition: &AttributedForeignPredicateDefinition) -> TokenStream {
    // what to generate?
    // - a function that returns an appropriate version of QueryResult for the specified determinism, with the given body
    // - an extern "C" trampoline, that calls this guy after converting its arguments and making a context
    // - a register function
    // - TODO a documented frontend for calling from rust as if this is a query
    let def = definition.predicate.generate_definition();
    let (trampoline_name, trampoline) = definition.predicate.generate_trampoline();
    let registration = definition.predicate.generate_registration(
        &trampoline_name,
        &definition.visibility,
        definition.predicate_name.as_ref(),
        definition.predicate_module.as_ref(),
    );

    quote! {#def #trampoline #registration}
}

fn generate_definitions(block: &ForeignPredicateDefinitionBlock) -> TokenStream {
    let code = block
        .definitions
        .iter()
        .map(|definition| generate_definition(definition));
    quote! {#(#code)*}
}
