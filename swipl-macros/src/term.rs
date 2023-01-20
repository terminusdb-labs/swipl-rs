use proc_macro2::{Span, TokenStream};
use quote::quote;
use std::collections::HashMap;
use syn::ext::IdentExt;
use syn::parse::{Parse, ParseBuffer, Result};
use syn::punctuated::Punctuated;
use syn::token::{Bracket, Paren};
use syn::{
    bracketed, parenthesized, parse_macro_input, Expr, Ident, LitBool, LitFloat, LitInt, LitStr,
    Token,
};

use crate::util::*;

fn term_ident_from_id(id: usize) -> Ident {
    Ident::new(&format!("__swipl_term_ref_{}", id), Span::call_site())
}

/// expand into a series of term puts
pub fn term_macro(stream: proc_macro::TokenStream) -> proc_macro::TokenStream {
    //let stream: TokenStream = stream.into();
    //println!("{:#?}", stream);
    let definition = parse_macro_input!(stream as OuterTerm);

    let context = definition.context;

    let term_ident = term_ident_from_id(0);
    let mut vars = HashMap::new();
    let (_, code) = definition.term.generate(0, 1, &mut vars);

    let crt = crate_token();
    let gen = quote! {
        {
           let #term_ident = #context.new_term_ref();

            let __swipl_frame = #context.open_frame();

            let result: #crt::result::PrologResult<()> = (||{ #code Ok(()) })();

            match result {
                Ok(()) => {
                    __swipl_frame.close();
                    Ok(#term_ident)
                },
                Err(e) => {
                    __swipl_frame.discard();
                    Err(e)
                }
            }
        }
    };
    //println!("{:#?}", gen);
    gen.into()
}

struct OuterTerm {
    context: Ident,
    term: Term,
}

impl Parse for OuterTerm {
    fn parse(input: &ParseBuffer) -> Result<Self> {
        let context = input.parse()?;
        input.parse::<Token![:]>()?;
        let term = input.parse()?;

        Ok(Self { context, term })
    }
}

enum Term {
    Functor(Functor),
    List(List),
    Tuple(Tuple),
    Leaf(Leaf),
}

impl Term {
    fn generate(
        &self,
        into_id: usize,
        top: usize,
        var_map: &mut HashMap<String, usize>,
    ) -> (usize, TokenStream) {
        match self {
            Self::Functor(f) => f.generate(into_id, top, var_map),
            Self::List(l) => l.generate(into_id, top, var_map),
            Self::Tuple(c) => c.generate(into_id, top, var_map),
            Self::Leaf(l) => l.generate(into_id, top, var_map),
        }
    }
}

impl Parse for Term {
    fn parse(input: &ParseBuffer) -> Result<Self> {
        if input.peek(Ident) && input.peek2(Paren) {
            let f = input.parse::<Functor>()?;
            Ok(Self::Functor(f))
        } else if input.peek(Bracket) {
            let l = input.parse::<List>()?;
            Ok(Self::List(l))
        } else if input.peek(Paren) {
            let c = input.parse::<Tuple>()?;
            Ok(Self::Tuple(c))
        } else {
            let l = input.parse::<Leaf>()?;
            Ok(Self::Leaf(l))
        }
    }
}

enum Leaf {
    Atom(Ident),
    String(LitStr),
    Int(LitInt),
    Float(LitFloat),
    Bool(LitBool),
    Variable(Ident),
    TemplateExpr(Expr),
}

impl Leaf {
    fn generate(
        &self,
        into_id: usize,
        top: usize,
        vars: &mut HashMap<String, usize>,
    ) -> (usize, TokenStream) {
        let into = term_ident_from_id(into_id);
        let crt = crate_token();
        (
            top, // no term allocations happen here, so return same
            match self {
                Self::Atom(ident) => {
                    let ident_str = format!("{}", ident);
                    quote! {#into.unify(&#crt::atom::atomable(#ident_str))?;}
                }
                Self::String(s) => {
                    quote! {#into.unify(#s)?;}
                }
                Self::Int(i) => {
                    // terrible, but necessary?
                    let int_str = format!("{}", i);
                    if int_str.starts_with('-') {
                        quote! {#into.unify(#i as i64)?;}
                    } else {
                        quote! {#into.unify(#i as u64)?;}
                    }
                }
                Self::Float(f) => {
                    quote! {#into.unify(#f as f64)?;}
                }
                Self::Bool(b) => {
                    quote! {#into.unify(#b)?;}
                }
                Self::Variable(v) => {
                    let var_name = format!("{}", v);
                    if var_name == "_" {
                        // fully anonymous, should always yield a new var
                        // so we don't actually have to do anything, as that is what it already is.
                        quote! {}
                    } else if let Some(var_id) = vars.get(&var_name) {
                        let var_ident = term_ident_from_id(*var_id);
                        quote! {#into.unify(&#var_ident)?;}
                    } else {
                        vars.insert(var_name, into_id);
                        // this term is already a variable. No need to do anything.
                        quote! {}
                    }
                }
                Self::TemplateExpr(expr) => {
                    quote! {#into.unify(#expr)?;}
                }
            },
        )
    }
}

impl Parse for Leaf {
    fn parse(input: &ParseBuffer) -> Result<Self> {
        if input.peek(Token![#]) {
            // templating!
            input.parse::<Token![#]>().unwrap();

            let expr = input.parse::<Expr>()?;
            Ok(Self::TemplateExpr(expr))
        } else if input.peek(Token![_]) {
            Ok(Self::Variable(input.call(Ident::parse_any)?))
        } else if input.peek(Ident) {
            let ident = input.parse::<Ident>()?;
            let name = format!("{}", ident);
            let first_char = name.chars().next().unwrap();
            if first_char == '_' || first_char.is_uppercase() {
                Ok(Self::Variable(ident))
            } else {
                Ok(Self::Atom(ident))
            }
        } else if input.peek(LitStr) {
            Ok(Self::String(input.parse()?))
        } else if input.peek(LitInt) {
            Ok(Self::Int(input.parse()?))
        } else if input.peek(LitFloat) {
            Ok(Self::Float(input.parse()?))
        } else if input.peek(LitBool) {
            Ok(Self::Bool(input.parse()?))
        } else {
            Err(input.error("unknown leaf type"))
        }
    }
}

struct Functor {
    head: Ident,
    params: Vec<Term>,
}

impl Functor {
    fn generate(
        &self,
        into_id: usize,
        mut top: usize,
        vars: &mut HashMap<String, usize>,
    ) -> (usize, TokenStream) {
        let crt = crate_token();
        let into = term_ident_from_id(into_id);
        let arity = self.params.len();
        let head_str = format!("{}", self.head);

        let functor_put = quote! {
            {
                let functor = #crt::functor::Functor::new(#head_str, std::convert::TryInto::try_into(#arity).unwrap());
                #into.unify(&functor)?;
            }
        };

        let param_assign = match arity > 0 {
            true => {
                let term_id_ident = Ident::new(
                    &format!("__swipl_ident_refs_{}", top + 1),
                    Span::call_site(),
                );
                let term_id = top + 1;
                let term_idents: Vec<_> = (0..arity)
                    .map(|i| term_id + i)
                    .map(term_ident_from_id)
                    .collect();

                top += arity + 1;
                let terms_init = term_idents.iter().enumerate().map(|(ix, ident)| {
                    quote! {
                        let #ident = unsafe {__swipl_frame.wrap_term_ref(#term_id_ident + #ix)};
                        #into.unify_arg(#ix+1, &#ident)?;
                    }
                });

                let mut terms_fill = Vec::with_capacity(arity);
                for (i, p) in self.params.iter().enumerate() {
                    let (new_top, gen) = p.generate(term_id + i, top, vars);
                    top = new_top;
                    terms_fill.push(gen);
                }

                quote! {
                    let #term_id_ident = unsafe { #crt::fli::PL_new_term_refs(std::convert::TryInto::try_into(#arity).unwrap()) };
                    #(#terms_init)*

                    #(#terms_fill)*
                }
            }
            false => quote! {},
        };

        (
            top,
            quote! {
                #functor_put
                #param_assign
            },
        )
    }
}

impl Parse for Functor {
    fn parse(input: &ParseBuffer) -> Result<Self> {
        let head = input.parse()?;

        let params_stream;
        parenthesized!(params_stream in input);
        let params_punct: Punctuated<Term, Token![,]> =
            params_stream.parse_terminated(Term::parse)?;
        let params: Vec<_> = params_punct.into_iter().collect();

        Ok(Self { head, params })
    }
}

struct List {
    elements: Vec<Term>,
}

impl List {
    fn generate(
        &self,
        into_id: usize,
        mut top: usize,
        vars: &mut HashMap<String, usize>,
    ) -> (usize, TokenStream) {
        let crt = crate_token();
        let into = term_ident_from_id(into_id);
        let len = self.elements.len();

        // create term names for all the elements
        let term_id_ident = Ident::new(&format!("__swipl_ident_refs_{}", top), Span::call_site());
        let term_id = top + 1;
        let term_idents: Vec<_> = (0..len)
            .map(|i| term_id + i)
            .map(term_ident_from_id)
            .collect();

        top += len;

        let elements_assign = match len > 0 {
            true => {
                // initialize terms
                let terms_init = term_idents.iter().enumerate().map(|(ix, ident)| {
                    quote! {
                        let #ident = unsafe {__swipl_frame.wrap_term_ref(#term_id_ident + #ix)};
                    }
                });

                // one extra for the term_id_ident ref
                top += 1;

                // generate code for term construction
                let mut terms_fill = Vec::with_capacity(len);
                for (i, e) in self.elements.iter().enumerate() {
                    let (new_top, gen) = e.generate(term_id + i, top, vars);
                    top = new_top;
                    terms_fill.push(gen);
                }

                quote! {
                    let #term_id_ident = unsafe { #crt::fli::PL_new_term_refs(std::convert::TryInto::try_into(#len).unwrap()) };
                    #(#terms_init)*

                    #(#terms_fill)*
                }
            }
            false => quote! {},
        };

        // build up list
        (
            top,
            quote! {
                #elements_assign

                let arr = [#(&#term_idents),*];
                #into.unify(arr.as_ref())?;
            },
        )
    }
}

impl Parse for List {
    fn parse(input: &ParseBuffer) -> Result<Self> {
        let elements_stream;
        bracketed!(elements_stream in input);
        let elements_punct: Punctuated<Term, Token![,]> =
            elements_stream.parse_terminated(Term::parse)?;
        let elements: Vec<_> = elements_punct.into_iter().collect();

        Ok(Self { elements })
    }
}

struct Tuple {
    terms: Vec<Term>,
}

impl Tuple {
    fn generate(
        &self,
        into_id: usize,
        mut top: usize,
        vars: &mut HashMap<String, usize>,
    ) -> (usize, TokenStream) {
        let len = self.terms.len();

        if len == 1 {
            // this is not actually a tuple. Just chain into generating the term
            return self.terms[0].generate(into_id, top, vars);
        }

        let crt = crate_token();
        let into = term_ident_from_id(into_id);

        // create term names for all the elements
        let term_id_ident = Ident::new(&format!("__swipl_ident_refs_{}", top), Span::call_site());
        let term_id = top + 1;
        let term_idents: Vec<_> = (0..len)
            .map(|i| term_id + i)
            .map(term_ident_from_id)
            .collect();

        // initialize terms
        let terms_init = term_idents.iter().enumerate().map(|(ix, ident)| {
            quote! {
                let #ident = unsafe {__swipl_frame.wrap_term_ref(#term_id_ident + #ix)};
            }
        });

        top += len + 1;

        // generate code for term construction
        let mut terms_fill = Vec::with_capacity(len);
        for (i, e) in self.terms.iter().enumerate() {
            let (new_top, gen) = e.generate(term_id + i, top, vars);
            top = new_top;
            terms_fill.push(gen);
        }

        let terms_assign = quote! {
            let #term_id_ident = unsafe { #crt::fli::PL_new_term_refs(std::convert::TryInto::try_into(#len).unwrap()) };
            #(#terms_init)*

            #(#terms_fill)*
        };

        let final_setup = quote! {
            let cur_ident = __swipl_frame.new_term_ref();
            cur_ident.unify(&#into)?;

            let comma_functor = #crt::functor::Functor::new(",", 2);
            cur_ident.unify(&comma_functor)?;
        };

        let mut terms_chain = Vec::with_capacity(len);
        for term_ident in term_idents.iter() {
            // for each element except the last one, we need to
            // - unify comma functor with current
            // - unify element with first
            // - make current the second element
            terms_chain.push(quote! {
                cur_ident.unify(&comma_functor)?;
                cur_ident.unify_arg(1, &#term_ident)?;
                let next_ident = __swipl_frame.new_term_ref();
                cur_ident.unify_arg(2, &next_ident)?;
                cur_ident.put(&next_ident)?;
            });
        }

        // for the last element, we only need to put it in the second position
        let last_elt = &term_idents[len - 1];
        terms_chain.push(quote! {
            cur_ident.unify(&#last_elt)?;
        });

        // build up tuple
        (
            top,
            quote! {
                #terms_assign

                #final_setup
                #(#terms_chain)*
            },
        )
    }
}

impl Parse for Tuple {
    fn parse(input: &ParseBuffer) -> Result<Self> {
        let terms_stream;
        parenthesized!(terms_stream in input);
        let terms_punct: Punctuated<Term, Token![,]> =
            terms_stream.parse_terminated(Term::parse)?;
        let terms: Vec<_> = terms_punct.into_iter().collect();
        if terms.is_empty() {
            terms_stream
                .error("parenthesized list of expressions should contain at least one element");
        }

        Ok(Self { terms })
    }
}
