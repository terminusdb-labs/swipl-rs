//! swipl-macros provides procedural macros for the swipl crate.

mod kw;
mod util;

mod blob;
mod pred;
mod predicate;
mod prolog;
mod term;

use proc_macro::TokenStream;

/// Define prolog predicates to be used from rust code.
///
/// The `prolog!` macro takes a block of function declaration. Each
/// declaration is of the format `fn <predicate>(..args..);`, where
/// args is a list of argument names. Optionally, a visibility
/// specifier like `pub` may be used. This much like an ordinary rust
/// function declaration, except that the arguments are typeless.
///
/// Each function may be annotated with a `#[name("..name..")]`
/// attribute, which specifies what the name of this predicate is in
/// prolog. When omitted, the function name will be used.
///
/// Each function may be annotated with a `#[module("..module..")]`
/// attribute, which specifies what prolog module this predicate is
/// in.  When omitted, no module is assumed.
///
/// For each function declaration, a function will be generated which
/// takes a context argument, followed by all declared arguments, and
/// returns a query opened in that context.
///
/// Example:
/// ```ignore
/// prolog! {
///     fn writeq(term);
///     #[name("nl")]
///     fn print_a_newline();
///     #[module("zlib")]
///     pub fn zopen(stream, zstream, options);
/// }
/// ```
#[proc_macro]
pub fn prolog(stream: TokenStream) -> TokenStream {
    prolog::prolog_macro(stream).into()
}

/// Generate an inline callable predicate.
///
/// Predicates are specified in prolog style. You can either use the
/// syntax `predicate/arity` or `module:predicate/arity`.
///
/// This macro will generate code that generates a `CallablePredicate`
/// object. The actual prolog predicate is only looked up at first
/// call of this generated code. Each subsequent call will reuse the
/// lookup.
///
/// example:
/// ```ignore
/// let writeq = pred!(writeq/1);
/// context.call_once(writeq, [&term])?;
/// ```
/// ```ignore
/// context.call_once(pred!(user:nl/0), [])?;
/// ```
#[proc_macro]
pub fn pred(stream: TokenStream) -> TokenStream {
    pred::pred_macro(stream).into()
}

/// Define foreign predicates written in rust for use in prolog.
///
/// The `predicates!` macro takes an arbitrary amount of predicate
/// definitions. These definitions may be semidet or
/// nondet. Optionally, a visibility specifier like `pub` may be used
/// to change the visibility of the generated functions. These
/// definitions look somewhat like ordinary rust functions. However,
/// their argument list is completely untyped, as each argument is
/// known to be a `&Term`, except for the first argument which is a
/// context object. As there always needs to be a context to call a
/// predicate, this first argument is required, even if it is unused.
///
/// For each definition, a registration function will be
/// generated. This function will be named `register_<name>`, where
/// name is the name of the defined predicate, and this function will
/// take zero arguments. After calling this function, the predicate is
/// registered and may be used from prolog code.
///
/// Each definition may optionally be annotated with
/// `#[module("<module>")]` and/or `#[name("<name>")]` To change the
/// module this predicate will be registered in, or the name of the
/// predicate in prolog. By default, the predicate name will be the
/// definition name, and the module will be the context module at the
/// time of generation. For foreign libraries, this context module is
/// whatever module did the first import of this library. Otherwise
/// it's usually 'user'.
///
/// # Semideterministic predicates
/// The first kind of predicate that you can define is a semidet
/// predicate. Semidet, or semideterministic, means that this
/// predicate is only going to have one result, and it could either be
/// success or failure. Note that this also covers the deterministic
/// case - to implement a deterministic predicate, just ensure that
/// your predicate does not fail.
///
/// Semidet predicates return a `PrologResult<()>`, which also happens
/// to be the type returned by most of the functions in the `swipl`
/// library. This means you can easily handle failure and exception of
/// things you call using rust's `?` syntax, or make use of the various combinators that are defined on `context` objects and in the `result` module.
///
/// ## Examples
/// ```ignore
/// predicates! {
///     semidet fn unify_with_foo(context, term) {
///         let atom = context.new_atom("foo");
///         term.unify(&atom)
///     }
///
///     #[module("some_module")]
///     #[name("some_alternate_name")]
///     pub semidet fn term_is_42(_context, term) {
///         let num: u64 = term.get::<u64>()?;
///
///         into_prolog_result(num == 42)
///     }
///
///     semidet fn just_fail(_context) {
///         Err(PrologError::Failure)
///     }
///
///     pub semidet fn throw_if_not_42(_context, term) {
///         let num: u64 = term.get::<u64>()?;
///         if num != 42 {
///             context.raise_exception(&term!{context: error(this_is_not_the_answer, _)})
///         } else {
///             Ok(())
///         }
///     }
/// }
/// ```
/// To register these defined predicates, their register function has to be called:
/// ```ignore
/// register_unify_with_foo();
/// register_term_is_42();
/// register_just_fail();
/// register_throw_if_not_42();
/// ```
///
/// # Nondeterministic predicates
/// Nondet or nondeterministic predicates are a bit more complex to
/// implement. Instead of just one block which returns success or
/// failure, nondet predicates are implemented with two bodies, a
/// setup block and a call block.
///
/// In the setup block, you create a state object which will be
/// available in the call block. The call block is then called with
/// this state object. As long as the call block returns true, the
/// predicate call is considered to still have choice points and will
/// be called unless the caller does a cut, which will clean up the
/// state object automatically.
///
/// ## The state type
/// Nondeterministic predicate definitions require you to specify a
/// type argument as part of the function signature. This specifies
/// the type of the state object, and is required to implement the
/// auto-traits `Send` and `Unpin`.
///
/// ## Setup
/// The setup block is called at the start of a predicate
/// invocation. It is to return a `PrologResult<Option<StateObject>>`,
/// where `StateObject` is your state object type.
///
/// You can return from this block in three ways:
/// - Return an exception or failure. The predicate will error or fail accordingly and the call block will not be invoked.
/// - Return `None`. The call block will also not be invoked, but the
/// predicate will return success. This is useful to handle predicate
/// inputs which allow your predicate to behave in a semidet manner.
/// - Return `Some(object)`. This returns a state object for use in
/// the call block. After this, the call block will be invoked.
///
/// ## Call
/// The call block is called each time the next result is required from this predicate. This happens on the first call to this predicate (except if the setup returned early as described above), and subsequently upon backtracking. The call block is given a mutable borrow of the state object, and is therefore able to both inspect and modify it.
///
/// you can return from this block in three ways:
/// - Return an exception or failure. Thep redicate will error or fail accordingly, and the call block will not be invoked again.
/// - Return false, signaling that this was the last succesful call to this predicate.
/// - Return true, signaling that there's more results available upon backtracking.
///
/// After exception, failure or returning false to signal the last succesful call, the state object will be cleaned up automatically.
///
/// ## Examples
/// ```ignore
/// predicates!{
///     nondet fn unify_with_bar_baz<Vec<String>>(context, term) {
///         setup => {
///             Ok(Some(vec!["bar", "baz"]))
///         },
///         call(v) => {
///             let next = v.pop().unwrap();
///             let atom = context.new_atom(next);
///             term.unify(&atom)?;
///
///             Ok(!v.is_empty())
///         }
///     }
///
///     nondet fn fail_early<()>(_context) {
///         setup => {
///             Err(PrologError::Failure)
///         },
///         call(_) => {
///             // We never get here
///         }
///     }
///
///     nondet fn succeed_early<()>(_context) {
///         setup => {
///             Ok(None)
///         },
///         call(_) => {
///             // We never get here
///         }
///     }
/// }
/// ```
#[proc_macro]
pub fn predicates(stream: TokenStream) -> TokenStream {
    predicate::predicates_macro(stream).into()
}

/// Generate a term from a rust expression.
///
/// This macro takes two arguments, a context to generate the term in,
/// and a rust expression representing the prolog term to generate..
///
/// The macro returns a `PrologResult<Term>` containing new term,
/// created through `context.new_term_ref()`, which contains a prolog
/// term corresponding to the description. The `term!` macro cannot
/// actually fail with a PrologFailure, but it is possible for a
/// resource limit exception to be triggered by one of the underlying
/// calls into prolog.
///
/// # Examples
/// Generate a nested functor term:
/// ```ignore
/// let term = term!{context: foo(bar(baz, quux))}?;
///```
///
/// Embed a value in the term:
/// ```ignore
/// let num = 42;
/// let term = term!{context: foo(#42)}?;
/// ```
///
/// Embed a term in the term:
/// ```ignore
/// let inner = context.new_term_ref();
/// let term = term!{context: foo(#&inner)}?;
/// ```
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
