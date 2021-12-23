//! Prolog terms.
//!
//! In prolog, all data is a term. Terms are things like atoms or
//! numbers, or compound structures like functors, lists,
//! dictionaries, or tuples. Even prolog code itself is a term.
//!
//! Interaction with SWI-Prolog terms happens through so-called term
//! references. These term references live on the prolog stack, and
//! they contain a term.
//!
//! If we have a term reference, we can get data from it, and put data
//! into it. Furthermore, we can unify terms with eachother, or we can
//! unify a term with user data.
//!
//! As term references live on a stack, they aren't valid
//! forever. They're only valid as long as the frame in which they are
//! created is still around.
//!
//! swipl-rs has been written to make working with terms easy. First,
//! through lifetimes, it is always ensured that you can only work
//! with terms that are still in scope. As soon as a frame goes out of
//! context, trying to use a term that was created by that frame will
//! result in a compile error.
//!
//! Second, getting data into and out of terms can all be done through
//! a unified interface on `Term`. This interface is extendable with
//! your own types that you wish to get into or out of prolog.
//!
//! Third, swipl-rs supports construction of complex terms through the
//! [term!](crate::prelude::term!) macro. Consider using this macro when
//! you have to produce deeply nested types.
use super::atom::*;
use super::context::*;
use super::engine::*;
use super::fli::*;
use super::result::*;
use std::convert::TryInto;
use std::fmt;
use std::fmt::Debug;
use std::os::raw::c_char;

use swipl_macros::term;

/// A term reference.
#[derive(Clone)]
pub struct Term<'a> {
    term: term_t,
    origin: TermOrigin<'a>,
}

impl<'a> Debug for Term<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(fmt, "Term({:?})", self.term)
    }
}

impl<'a> Term<'a> {
    pub(crate) unsafe fn new(term: term_t, origin: TermOrigin<'a>) -> Self {
        Term { term, origin }
    }

    /// Return the underying `term_t` from the SWI-Prolog fli.
    pub fn term_ptr(&self) -> term_t {
        self.term
    }

    /// Returns true if this term reference holds a variable.
    pub fn is_var(&self) -> bool {
        self.assert_term_handling_possible();
        unsafe { PL_is_variable(self.term) != 0 }
    }

    /// Reset terms created after this term, including this term itself.
    /// Only safe to call when you're sure these terms aren't used afterwards.
    pub unsafe fn reset(&self) {
        self.assert_term_handling_possible();
        PL_reset_term_refs(self.term);
    }

    /// Assert that the engine where this term was originally created is the active engine on this thread.
    pub fn assert_term_handling_possible(&self) {
        if !self.origin.is_engine_active() {
            panic!("term is not part of the active engine");
        }
    }

    /// Unify this term with some unifiable data.
    ///
    /// [Unifiable] is a trait that has been implemented for many data
    /// types.
    ///
    /// This will return an `Err(PrologError::Exception)` if during
    /// unification, an error was raised somewhere in the SWI-Prolog
    /// fli. If unification is not possible, an
    /// `Err(PrologError::Failure)` will be returned. Otherwise the
    /// result is an `Ok(())`.
    pub fn unify<U: Unifiable>(&self, unifiable: U) -> PrologResult<()> {
        let result = unifiable.unify(self);

        // unify functions may throw an exception, either directly or
        // through some inner function. It's too much hassle to have
        // each function check for themselves and return the
        // appropriate thing, so we just do it all here.
        if unsafe { PL_exception(0) != 0 } {
            Err(PrologError::Exception)
        } else if result {
            Ok(())
        } else {
            Err(PrologError::Failure)
        }
    }

    /// Unify the nth arg of the term with some unifiable data. This
    /// assumes that the given term contains a functor.
    ///
    /// The argument position is 1-indexed. Therefore, the first
    /// argument is argument 1.
    ///
    /// This will return an `Err(PrologError::Exception)` if during
    /// unification, an error was raised somewhere in the SWI-Prolog
    /// fli. If unification is not possible (which may be because this
    /// term does not hold a functor), an `Err(PrologError::Failure)`
    /// will be returned. Otherwise the result is an `Ok(())`.
    pub fn unify_arg<U: Unifiable>(&self, index: usize, unifiable: U) -> PrologResult<()> {
        if index == 0 {
            panic!("unify_arg was given index 0, but index starts at 1");
        }

        self.assert_term_handling_possible();

        let arg_ref = unsafe { PL_new_term_ref() };

        let result = unsafe { PL_get_arg(index.try_into().unwrap(), self.term, arg_ref) };
        if unsafe { PL_exception(0) != 0 } {
            return Err(PrologError::Exception);
        }

        let arg = unsafe { Term::new(arg_ref, self.origin.clone()) };
        let mut result2 = Err(PrologError::Failure);
        if result != 0 {
            result2 = arg.unify(unifiable);
        }

        unsafe { PL_reset_term_refs(arg_ref) };

        result2
    }

    /// Retrieve data from the term reference.
    ///
    /// Any data type for which [TermGetable] has been implemented may
    /// be retrieved in this way.
    ///
    /// This will return an `Err(PrologError::Exception)` if during
    /// getting, an error was raised somewhere in the SWI-Prolog
    /// fli. If getting is not possible (because the term holds a
    /// variable, or an incompatible data type), an
    /// `Err(PrologError::Failure)` will be returned. Otherwise the
    /// result is an `Ok(data)`, with the requested data in it.
    pub fn get<G: TermGetable>(&self) -> PrologResult<G> {
        let opt = G::get(self);

        // get functions may throw an exception, either directly or
        // through some inner function. It's too much hassle to have
        // each function check for themselves and return the
        // appropriate thing, so we just do it all here.
        if unsafe { PL_exception(0) != 0 } {
            Err(PrologError::Exception)
        } else if opt.is_none() {
            Err(PrologError::Failure)
        } else {
            Ok(opt.unwrap())
        }
    }

    /// Retrieve data from the term reference, or raise exception if
    /// this is impossible.
    ///
    /// Any data type for which [TermGetable] has been implemented may
    /// be retrieved in this way.
    ///
    /// In addition to the situations where `get()` would raise an
    /// exception, this will raise an `error(instantiation_error, _)`
    /// when called on an unbound term, and `error(type_error(<type
    /// name>, <term>), _)` when retrieving the value from the term
    /// was not possible, which is always assumed to be due to a type
    /// incompatibility.
    ///
    /// Therefore, the only way this function will error is with an
    /// exception. It will never return a failure.
    pub fn get_ex<G: TermGetable>(&self) -> PrologResult<G> {
        if self.is_var() {
            let context = unsafe { unmanaged_engine_context() };
            let reset_term = context.new_term_ref();
            let exception_term = term! {context: error(instantiation_error, _)};
            let result = exception_term.and_then(|t| context.raise_exception(&t));
            unsafe { reset_term.reset() };

            return result;
        }
        let opt = G::get(self);

        // get functions may throw an exception, either directly or
        // through some inner function. It's too much hassle to have
        // each function check for themselves and return the
        // appropriate thing, so we just do it all here.
        if unsafe { PL_exception(0) != 0 } {
            Err(PrologError::Exception)
        } else if opt.is_none() {
            let context = unsafe { unmanaged_engine_context() };
            let reset_term = context.new_term_ref();
            let type_name = Atomable::from(G::name());
            let exception_term = term! {context: error(type_error(#type_name, #self), _)};
            let result = exception_term.and_then(|t| context.raise_exception(&t));
            unsafe { reset_term.reset() };

            result
        } else {
            Ok(opt.unwrap())
        }
    }

    /// Retrieve data from the nth position of the given term. This
    /// assumes that the given term contains a functor.
    ///
    /// The argument position is 1-indexed. Therefore, the first
    /// argument is argument 1.
    ///
    /// This will return an `Err(PrologError::Exception)` if during
    /// getting, an error was raised somewhere in the SWI-Prolog
    /// fli. If getting is not possible (because the term holds a
    /// variable, or an incompatible data type), an
    /// `Err(PrologError::Failure)` will be returned. Otherwise the
    /// result is an `Ok(data)`, with the requested data in it.
    pub fn get_arg<G: TermGetable>(&self, index: usize) -> PrologResult<G> {
        if index == 0 {
            panic!("unify_arg was given index 0, but index starts at 1");
        }

        self.assert_term_handling_possible();

        let arg_ref = unsafe { PL_new_term_ref() };

        let result = unsafe { PL_get_arg(index.try_into().unwrap(), self.term, arg_ref) };
        if unsafe { PL_exception(0) != 0 } {
            return Err(PrologError::Exception);
        }

        let arg = unsafe { Term::new(arg_ref, self.origin.clone()) };
        let mut result2 = Err(PrologError::Failure);
        if result != 0 {
            result2 = arg.get();
        }

        unsafe { PL_reset_term_refs(arg_ref) };

        result2
    }

    /// Retrieve a &str from this term, and call the given function with it.
    ///
    /// This allows you to extract a string from a prolog string with
    /// as few copies as possible.
    pub fn get_str<R, F>(&self, func: F) -> PrologResult<R>
    where
        F: Fn(Option<&str>) -> R,
    {
        self.assert_term_handling_possible();
        let mut ptr = std::ptr::null_mut();
        let mut len = 0;
        let result = unsafe {
            PL_get_nchars(
                self.term,
                &mut len,
                &mut ptr,
                (CVT_STRING | REP_UTF8).try_into().unwrap(),
            )
        };

        if unsafe { PL_exception(0) != 0 } {
            return Err(PrologError::Exception);
        }

        let arg = if result == 0 {
            None
        } else {
            let swipl_string_ref =
                unsafe { std::slice::from_raw_parts(ptr as *const u8, len as usize) };

            let swipl_string = std::str::from_utf8(swipl_string_ref).unwrap();

            Some(swipl_string)
        };

        Ok(func(arg))
    }

    /// Retrieve an atom from this term, and call the given function with a borrow to it.
    ///
    /// We skip reference-counting for this atom which may be slightly
    /// faster in some scenarios.
    pub fn get_atom<R, F>(&self, func: F) -> PrologResult<R>
    where
        F: Fn(Option<&Atom>) -> R,
    {
        self.assert_term_handling_possible();
        unsafe { get_atom(self, func) }
    }

    /// Retrieve an atom from this term, and call the given function with a borrow to it.
    ///
    /// We skip reference-counting for this atom which may be slightly
    /// faster in some scenarios.
    pub fn get_atom_name<R, F>(&self, func: F) -> PrologResult<R>
    where
        F: Fn(Option<&str>) -> R,
    {
        self.assert_term_handling_possible();
        let mut ptr = std::ptr::null_mut();
        let mut len = 0;
        let result = unsafe {
            PL_get_nchars(
                self.term,
                &mut len,
                &mut ptr,
                (CVT_ATOM | REP_UTF8).try_into().unwrap(),
            )
        };

        if unsafe { PL_exception(0) != 0 } {
            return Err(PrologError::Exception);
        }

        let arg = if result == 0 {
            None
        } else {
            let swipl_string_ref =
                unsafe { std::slice::from_raw_parts(ptr as *const u8, len as usize) };

            let swipl_string = std::str::from_utf8(swipl_string_ref).unwrap();

            Some(swipl_string)
        };

        Ok(func(arg))
    }

    /// Put data into the term reference using a borrow.
    ///
    /// Any data type for which [TermPutable] has been implemented may
    /// be put into a term ref in this way.
    ///
    /// This is a nonlogical operation. The term reference will
    /// replace its content in a way that does not play nicely with
    /// backtracking.
    ///
    /// This will return an `Err(PrologException)` if during putting,
    /// an error was raised somewhere in the SWI-Prolog
    /// fli. Otherwise, the result is `Ok(())`.
    pub fn put<T: TermPutable + ?Sized>(&self, val: &T) -> NonFailingPrologResult<()> {
        val.put(self);

        if unsafe { PL_exception(0) != 0 } {
            Err(PrologException)
        } else {
            Ok(())
        }
    }

    /// Put data into the term reference using a copyable value.
    ///
    /// Any data type for which [TermPutable] has been implemented may
    /// be put into a term ref in this way.
    ///
    /// This is a nonlogical operation. The term reference will
    /// replace its content in a way that does not play nicely with
    /// backtracking.
    ///
    /// This will return an `Err(PrologException)` if during putting,
    /// an error was raised somewhere in the SWI-Prolog
    /// fli. Otherwise, the result is `Ok(())`.
    pub fn put_val<T: TermPutable>(&self, val: T) -> NonFailingPrologResult<()> {
        self.put(&val)
    }
}

#[derive(Clone)]
pub(crate) struct TermOrigin<'a> {
    engine: PL_engine_t,
    _lifetime: std::marker::PhantomData<&'a ()>,
}

impl<'a> TermOrigin<'a> {
    pub unsafe fn new(engine: PL_engine_t) -> Self {
        Self {
            engine,
            _lifetime: Default::default(),
        }
    }
}

unsafe impl<'a> Send for TermOrigin<'a> {}
unsafe impl<'a> Sync for TermOrigin<'a> {}

impl<'a> TermOrigin<'a> {
    pub fn is_engine_active(&self) -> bool {
        is_engine_active(self.engine)
    }

    pub fn origin_engine_ptr(&self) -> PL_engine_t {
        self.engine
    }
}

/// Trait for term unification.
///
/// This is marked unsafe because in order to do term unification, we
/// must be sure that
/// - the term is created on the engine which is currently active
/// - the given context is a context for this engine
///
/// Not checking those preconditions results in undefined
/// behavior. Therefore, care must be taken to ensure that `unify` is
/// actually safe.
///
/// The macro [unifiable!] provides a way to safely implement this
/// trait by doing the precondition checks for you.
pub unsafe trait Unifiable {
    /// Unify this data with the given term reference.
    ///
    /// You'd generally not use this directly, but rather, go through [Term::unify].
    fn unify(&self, term: &Term) -> bool;
}

unsafe impl<T: Unifiable> Unifiable for &T {
    fn unify(&self, term: &Term) -> bool {
        (*self).unify(term)
    }
}

/// Trait for getting data from a term reference.
///
/// This is marked unsafe because in order to do term getting, we
/// must be sure that
/// - the term is created on the engine which is currently active
/// - the given context is a context for this engine
///
/// Not checking those preconditions results in undefined
/// behavior. Therefore, care must be taken to ensure that `get` is
/// actually safe.
///
/// The macro [term_getable!] provides a way to safely implement this
/// trait by doing the precondition checks for you.
pub unsafe trait TermGetable: Sized {
    /// Get data from a term reference.
    ///
    /// You'd generally not use this directly, but rather, go through [Term::get].
    fn get(term: &Term) -> Option<Self>;

    /// Get the name of this data type for use in exception reporting.
    fn name() -> &'static str;
}

/// Trait for putting data into a term reference.
///
/// Unlike unification, putting data into a term replaces the term
/// entirely. This is a non-logical operation that doesn't play nice
/// with backtracking. You're generally better off using unification.
///
/// This is marked unsafe because in order to do term putting, we
/// must be sure that
/// - the term is created on the engine which is currently active
/// - the given context is a context for this engine
///
/// Not checking those preconditions results in undefined
/// behavior. Therefore, care must be taken to ensure that `put` is
/// actually safe.
///
/// The macro [term_putable!] provides a way to safely implement this
/// trait by doing the precondition checks for you.
pub unsafe trait TermPutable {
    /// Put data into the term reference.
    ///
    /// You'd generally not use this directly, but rather, go through [Term::put].
    fn put(&self, term: &Term);
}

/// Easily implement [Unifiable].
///
/// Example:
/// ```
/// # use swipl::prelude::*;
/// struct Foo {num: u64}
///
/// unifiable!{
///     (self:Foo, term) => {
///         // Body needs to return a bool indicating success or failure.
///         // Failure may also be an exception. The wrapper will check for this.
///         attempt(term.unify(self.num)).unwrap_or(false)
///     }
/// }
///
/// fn do_something(term: &Term) -> PrologResult<()> {
///     term.unify(Foo{num:42})
/// }
/// ```
#[macro_export]
macro_rules! unifiable {
    (($self_:ident : $t:ty, $term_: ident) => $b: block) => {
        // unsafe justification: this macro inserts an assert in front
        // of the unification body, to ensure that we are given a term
        // that matches the given context, and that the currently
        // activated engine is one for which this term was created.
        unsafe impl<'a> Unifiable for $t {
            fn unify(&$self_, $term_: &Term) -> bool {
                $term_.assert_term_handling_possible();

                $b
            }
        }
    }
}

/// Easily implement [TermGetable].
///
/// Example:
/// ```
/// # use swipl::prelude::*;
/// struct Foo {num: u64}
///
/// term_getable!{
///     (Foo, term) => {
///         // Body needs to return an Option indicating success or failure.
///         // Failure may also be an exception. The wrapper will check for this.
///         let num: u64 = attempt_opt(term.get()).unwrap_or(None)?;
///         Some(Foo { num })
///     }
/// }
///
/// fn do_something(term: &Term) -> PrologResult<()> {
///     let foo: Foo = term.get()?;
///     println!("foo is {}", foo.num);
///     Ok(())
/// }
/// ```
#[macro_export]
macro_rules! term_getable {
    (($t:ty, $term_: ident) => $b: block) => {
        // unsafe justification: this macro inserts an assert in front
        // of the term get body, to ensure that we are given a term
        // that matches the given context, and that the currently
        // activated engine is one for which this term was created.
        unsafe impl<'a> TermGetable for $t {
            fn get($term_: &Term) -> Option<Self> {
                $term_.assert_term_handling_possible();

                $b
            }

            fn name() -> &'static str {
                stringify!($t)
            }
        }
    };

    (($t:ty, $name: tt, $term_: ident) => $b: block) => {
        // unsafe justification: this macro inserts an assert in front
        // of the term get body, to ensure that we are given a term
        // that matches the given context, and that the currently
        // activated engine is one for which this term was created.
        unsafe impl<'a> TermGetable for $t {
            fn get($term_: &Term) -> Option<Self> {
                $term_.assert_term_handling_possible();

                $b
            }

            fn name() -> &'static str {
                $name
            }
        }
    };
}

/// Easily implement [TermPutable].
///
/// Example:
/// ```
/// # use swipl::prelude::*;
/// struct Foo {num: u64}
///
/// term_putable!{
///     (self:Foo, term) => {
///         // body returns nothing, but underlying code may raise an exception on the prolog engine.
///         term.put(&self.num).unwrap_or(());
///     }
/// }
///
/// fn do_something(term: &Term) -> PrologResult<()> {
///     term.put(&Foo{num:42})?;
///     Ok(())
/// }
/// ```
#[macro_export]
macro_rules! term_putable {
    (($self_:ident : $t:ty, $term_: ident) => $b: block) => {
        // unsafe justification: this macro inserts an assert in front
        // of the term get body, to ensure that we are given a term
        // that matches the given context, and that the currently
        // activated engine is one for which this term was created.
        unsafe impl<'a> TermPutable for $t {
            fn put(&$self_, $term_: &Term) {
                $term_.assert_term_handling_possible();

                $b
            }
        }
    };
}

unifiable! {
    (self:Term<'a>, term) => {
        if self.origin.origin_engine_ptr() != term.origin.origin_engine_ptr() {
            panic!("terms being unified are not part of the same engine");
        }

        // unsafe justification: the fact that we have terms here means we are dealing with some kind of active context, and therefore an initialized swipl. The check above has made sure that both terms are part of the same engine too, and the unifiable! macro takes care of checking that we're on the correct engine.
        let result = unsafe { PL_unify(self.term, term.term) };

        // TODO we should actually properly test for an exception here.
        result != 0
    }
}

term_putable! {
    (self:Term<'a>, term) => {
        if self.origin.origin_engine_ptr() != term.origin.origin_engine_ptr() {
            panic!("terms being unified are not part of the same engine");
        }

        unsafe { PL_put_term(term.term, self.term); }
    }
}

unifiable! {
    (self:bool, term) => {
        let num = match self {
            true => 1,
            false => 0,
        };
        let result = unsafe { PL_unify_bool(term.term, num) };

        result != 0
    }
}

term_getable! {
    (bool, term) => {
        let mut out = 0;
        let result = unsafe { PL_get_bool(term.term, &mut out) };
        if result == 0 {
            None
        }
        else {
            Some(out != 0)
        }
    }
}

term_putable! {
    (self:bool, term) => {
        let bool_num: usize = match self {
            true => 1,
            false => 0
        };
        unsafe { PL_put_bool(term.term, bool_num.try_into().unwrap()) };
    }
}

unifiable! {
    (self:u64, term) => {
        // there's a possibility for this function to error, we need to check.
        // but there may already be an error waiting, so we need to stash that.

        // Note: this seems to be inconsistent with all the other
        // unify functions, but similar to the way the cvt
        // compatibility functions work.
        unsafe {with_cleared_exception(|| {
            let result = PL_unify_uint64(term.term, *self);
            let error_term_ref = PL_exception(0);
            if error_term_ref != 0 {
                let ctx = unmanaged_engine_context();
                let error_term = ctx.new_term_ref();
                PL_unify(error_term.term_ptr(), error_term_ref);
                PL_clear_exception();
                let comparison_term = match term!{ctx: error(type_error(integer, _), _)} {
                    Ok(t) => t,
                    // let wrapper pick up the error
                    Err(_) => return false
                };
                // really should be a non-unifying compare but meh
                if comparison_term.unify(&error_term).is_err() {
                    PL_raise_exception(error_term.term_ptr());
                }
                error_term.reset();
                false
            }
            else {
                result != 0
            }
        })}
    }
}

term_getable! {
    (u64, "integer", term) => {
        if unsafe { PL_is_integer(term.term) == 0 } {
            return None;
        }

        // there's a possibility for this function to error, we need to check.
        // but there may already be an error waiting, so we need to stash that.
        unsafe {with_cleared_exception(|| {
            let mut out = 0;
            let result = PL_cvt_i_uint64(term.term, &mut out);
            let error_term_ref = PL_exception(0);
            if error_term_ref != 0 {
                let ctx = unmanaged_engine_context();
                let error_term = ctx.new_term_ref();
                PL_unify(error_term.term_ptr(), error_term_ref);
                PL_clear_exception();
                let comparison_term = match term!{ctx: error(domain_error(not_less_than_zero, _), _)} {
                    Ok(r) => r,
                    // let wrapper pick up the error
                    Err(_) => return None
                };
                // really should be a non-unifying compare but meh
                if comparison_term.unify(&error_term).is_err() {
                    PL_raise_exception(error_term.term_ptr());
                }
                error_term.reset();
                None
            }
            else if result == 0 {
                None
            }
            else {
                Some(out)
            }
        })}
    }
}

term_putable! {
    (self:u64, term) => {
        unsafe { PL_put_uint64(term.term, *self) };
    }
}

unifiable! {
    (self:i64, term) => {
        let result = unsafe { PL_unify_int64(term.term, *self) };

        result != 0
    }
}

term_getable! {
    (i64, "integer", term) => {
        let mut out = 0;
        let result = unsafe { PL_get_int64(term.term, &mut out) };
        if result == 0 {
            None
        }
        else {
            Some(out)
        }
    }
}

term_putable! {
    (self:i64, term) => {
        unsafe { PL_put_int64(term.term, *self) };
    }
}

unifiable! {
    (self:f64, term) => {
        let result = unsafe { PL_unify_float(term.term, *self) };

        result != 0
    }
}

term_getable! {
    (f64, "float", term) => {
        let mut out = 0.0;
        let result = unsafe { PL_get_float(term.term, &mut out) };
        if result == 0 {
            None
        }
        else {
            Some(out)
        }
    }
}

term_putable! {
    (self:f64, term) => {
        unsafe { PL_put_float(term.term, *self) };
    }
}

unifiable! {
    (self:&str, term) => {
        let result = unsafe { PL_unify_chars(
            term.term_ptr(),
            (PL_STRING | REP_UTF8).try_into().unwrap(),
            self.len().try_into().unwrap(),
            self.as_bytes().as_ptr() as *const c_char,
        )
        };

        result != 0
    }
}

unifiable! {
    (self:String, term) => {
        let result = unsafe { PL_unify_chars(
            term.term_ptr(),
            (PL_STRING | REP_UTF8).try_into().unwrap(),
            self.len().try_into().unwrap(),
            self.as_bytes().as_ptr() as *const c_char,
        )
        };

        result != 0
    }
}

term_getable! {
    (String, "string", term) => {
        match term.get_str(|s|s.map(|s|s.to_owned())) {
            Ok(r) => r,
            // ignore error - it'll be picked up by the wrapper
            Err(_) => None
        }
    }
}

term_putable! {
    (self:str, term) => {
        unsafe { PL_put_chars(
            term.term_ptr(),
            (PL_STRING | REP_UTF8).try_into().unwrap(),
            self.len().try_into().unwrap(),
            self.as_bytes().as_ptr() as *const c_char,
        )
        };
    }
}

term_putable! {
    (self:String, term) => {
        unsafe { PL_put_chars(
            term.term_ptr(),
            (PL_STRING | REP_UTF8).try_into().unwrap(),
            self.len().try_into().unwrap(),
            self.as_bytes().as_ptr() as *const c_char,
        )
        };
    }
}

unifiable! {
    (self: &[u8], term) => {
        let result = unsafe { PL_unify_string_nchars(term.term_ptr(), self.len() as size_t, self.as_ptr() as *const i8) };

        result != 0
    }
}

term_getable! {
    (Vec<u8>, "string", term) => {
        let mut string_ptr = std::ptr::null_mut();
        let mut len = 0;
        let result = unsafe { PL_get_string(term.term_ptr(), &mut string_ptr, &mut len) };
        if result == 0 {
            return None;
        }

        let slice = unsafe { std::slice::from_raw_parts(string_ptr as *const u8, len as usize) };
        let mut result: Vec<u8> = Vec::with_capacity(len as usize);
        result.extend_from_slice(slice);

        Some(result)
    }
}

term_putable! {
    (self: [u8], term) => {
        unsafe { PL_put_string_nchars(term.term_ptr(), self.len() as size_t, self.as_ptr() as *const i8) };
    }

}

/// Unit struct representing an empty list in SWI-Prolog.
pub struct Nil;
unifiable! {
    (self:Nil, term) => {
        let result = unsafe { PL_unify_nil(term.term_ptr()) };

        result != 0
    }
}

term_getable! {
    (Nil, "list", term) => {
        let result = unsafe { PL_get_nil(term.term_ptr()) };

        match result != 0 {
            true => Some(Nil),
            false => None
        }
    }
}

term_putable! {
    (self:Nil, term) => {
        unsafe { PL_put_nil(term.term_ptr()); }
    }
}

unsafe impl<'a, T> Unifiable for &'a [T]
where
    &'a T: 'a + Unifiable,
{
    fn unify(&self, term: &Term) -> bool {
        term.assert_term_handling_possible();
        // let's create a fake context so we can make a frame
        // unsafe justification: This context will only exist inside this implementation. We know we are in some valid context for term handling, so that's great.
        let context = unsafe { unmanaged_engine_context() };

        let frame = context.open_frame();
        let list = frame.new_term_ref();

        if list.unify(term).is_err() {
            return false;
        }

        for t in self.iter() {
            // create a new frame to ensure we don't just keep putting head and tail refs on the stack.
            let frame2 = frame.open_frame();
            let head = frame2.new_term_ref();
            let tail = frame2.new_term_ref();

            // if list unification fails, or head can not be unified with current term,
            // return false early.
            // note: || is short-circuiting OR
            if unsafe { PL_unify_list(list.term_ptr(), head.term_ptr(), tail.term_ptr()) == 0 }
                || head.unify(t).is_err() {
                return false;
            }

            // reset term - should really be a method on term
            unsafe { PL_put_variable(list.term_ptr()) };

            if list.unify(tail).is_err() {
                return false;
            }

            frame2.close();
        }

        let success = unsafe { PL_unify_nil(list.term_ptr()) != 0 };
        frame.close();

        success
    }
}

unsafe impl<T: TermGetable> TermGetable for Vec<T> {
    fn get(term: &Term) -> Option<Self> {
        term.assert_term_handling_possible();

        let mut result: Vec<T> = Vec::new();

        // let's create a fake context so we can make a frame
        // unsafe justification: This context will only exist inside this implementation. We know we are in some valid context for term handling, so that's great.
        let context = unsafe { unmanaged_engine_context() };

        let frame = context.open_frame();
        let list = frame.new_term_ref();
        list.unify(term).unwrap();
        let mut success = true;
        loop {
            if unsafe { PL_get_nil(list.term_ptr()) != 0 } {
                break;
            }

            let frame2 = frame.open_frame();
            let head = frame2.new_term_ref();
            let tail = frame2.new_term_ref();
            success =
                unsafe { PL_get_list(list.term_ptr(), head.term_ptr(), tail.term_ptr()) != 0 };

            if !success {
                break;
            }

            let elt = head.get();
            if elt.is_err() {
                success = false;
                break;
            }

            result.push(elt.unwrap());

            // reset term - should really be a method on term
            unsafe { PL_put_variable(list.term_ptr()) };
            list.unify(tail).unwrap();
            frame2.close();
        }

        frame.close();

        match success {
            true => Some(result),
            false => None,
        }
    }

    fn name() -> &'static str {
        "list"
    }
}

#[cfg(test)]
mod tests {
    use crate::context::*;
    use crate::engine::*;
    use crate::result::*;

    #[test]
    fn unify_some_terms_with_success() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = context.new_term_ref();
        let term2 = context.new_term_ref();
        assert!(term1.unify(42_u64).is_ok());
        assert!(term2.unify(42_u64).is_ok());
        assert!(term1.unify(&term2).is_ok());
    }

    #[test]
    fn unify_some_terms_with_failure() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = context.new_term_ref();
        let term2 = context.new_term_ref();
        assert!(term1.unify(42_u64).is_ok());
        assert!(term2.unify(43_u64).is_ok());
        assert!(!term1.unify(&term2).is_ok());
    }

    #[test]
    fn unify_twice_different_failure() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.new_term_ref();
        assert!(term.unify(42_u64).is_ok());
        assert!(!term.unify(43_u64).is_ok());
    }

    #[test]
    fn unify_twice_different_with_rewind_success() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();
        let term = context.new_term_ref();
        let context2 = context.open_frame();

        assert!(term.unify(42_u64).is_ok());
        context2.rewind();
        assert!(term.unify(43_u64).is_ok());
    }

    #[test]
    fn unify_and_get_bools() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = context.new_term_ref();
        assert!(term1.get::<bool>().unwrap_err().is_failure());
        term1.unify(true).unwrap();
        assert_eq!(true, term1.get::<bool>().unwrap());
        let term2 = context.new_term_ref();
        term2.unify(false).unwrap();
        assert_eq!(false, term2.get::<bool>().unwrap());
    }

    #[test]
    fn unify_and_get_u64s() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = context.new_term_ref();
        assert!(term1.get::<u64>().unwrap_err().is_failure());
        term1.unify(42_u64).unwrap();
        assert_eq!(42, term1.get::<u64>().unwrap());
        let term2 = context.new_term_ref();
        term2.unify(0xffffffff_u64).unwrap();
        assert_eq!(0xffffffff, term2.get::<u64>().unwrap());
        let term3 = context.new_term_ref();
        term3.unify(0xffffffffffffffff_u64).unwrap();
        assert_eq!(0xffffffffffffffff, term3.get::<u64>().unwrap());
    }

    #[test]
    fn put_and_get_u64s() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = context.new_term_ref();
        assert!(term1.get::<u64>().unwrap_err().is_failure());
        term1.put_val(42_u64).unwrap();
        assert_eq!(42, term1.get::<u64>().unwrap());
    }

    #[test]
    fn unify_and_get_string_refs() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = context.new_term_ref();
        term1.get_str(|s| assert!(s.is_none())).unwrap();
        term1.unify("hello there").unwrap();
        term1
            .get_str(|s| assert_eq!("hello there", s.unwrap()))
            .unwrap();
    }

    #[test]
    fn unify_and_get_strings() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = context.new_term_ref();
        assert!(term1.get::<String>().unwrap_err().is_failure());
        term1.unify("hello there").unwrap();
        assert_eq!("hello there", term1.get::<String>().unwrap());
    }

    #[test]
    fn unify_and_get_different_types_fails() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = context.new_term_ref();
        term1.unify(42_u64).unwrap();
        assert!(term1.get::<bool>().unwrap_err().is_failure());
    }

    #[test]
    fn unify_list() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.new_term_ref();
        assert!(term.unify([42_u64, 12, 3, 0, 5].as_ref()).is_ok());

        assert_eq!(
            [42_u64, 12, 3, 0, 5].as_ref(),
            term.get::<Vec<u64>>().unwrap()
        );
    }

    #[test]
    fn unify_term_list() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.new_term_ref();
        let elt1 = context.new_term_ref();
        let elt2 = context.new_term_ref();
        elt1.unify(42_u64).unwrap();
        elt2.unify(43_u64).unwrap();
        assert!(term.unify([elt1, elt2].as_ref()).is_ok());

        assert_eq!([42_u64, 43].as_ref(), term.get::<Vec<u64>>().unwrap());
    }

    use crate::term;

    #[test]
    fn create_nested_functor_term() -> PrologResult<()> {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let var_term = context.new_term_ref();
        let _term = term! {context: foo(bar([a,b,42], baz(42, (1,((3)),true), #&var_term), quux(Var), quux2(Var)), "hi", yay(OtherVar, #&var_term), _, _, _a, _a)}?;
        var_term.unify(crate::atom::atomable("hallo")).unwrap();

        // TODO actually query this term for validity
        Ok(())
    }

    #[test]
    fn throw_error() -> PrologResult<()> {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let error_term = term! {context: error(some_error, _)}?;
        context.raise_exception::<()>(&error_term).unwrap_err();
        assert!(context.has_exception());

        Ok(())
    }

    #[test]
    fn work_with_binary_data_strings() -> PrologResult<()> {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let binary_data = vec![42, 0, 5];
        let term = context.new_term_ref();
        term.put(binary_data.as_slice())?;
        let retrieved: Vec<u8> = term.get()?;

        assert_eq!(binary_data, retrieved);

        term.unify(binary_data.as_slice())
    }
}
