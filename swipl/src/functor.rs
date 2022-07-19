//! Prolog functors.
//!
//! A functor is a core datatype in prolog. It is a combination of an
//! atom and an arity. Unlike atoms, functors are not
//! reference-counted and are never garbage collected.
//!
//! This module provides functions and types for interacting with
//! prolog functors.
use super::atom::*;
use super::consts::*;
use super::engine::*;
use super::fli::*;
use super::term::*;

use std::convert::TryInto;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::{term_getable, term_putable, unifiable};

/// A wrapper for a prolog functor.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Functor {
    functor: functor_t,
}

impl Functor {
    /// Wrap a `functor_t`, which is how the SWI-Prolog fli represents functors.
    ///
    /// This is unsafe because no check is done to ensure that the
    /// functor_t indeed points at a valid functor. The caller will
    /// have to ensure that this is the case.
    pub unsafe fn wrap(functor: functor_t) -> Self {
        Self { functor }
    }

    /// Create a new functor from the given name and arity.
    ///
    /// This will panic if no prolog engine is active on this thread.
    pub fn new<A: IntoAtom>(name: A, arity: u16) -> Functor {
        assert_some_engine_is_active();
        if arity as usize > MAX_ARITY {
            panic!("functor arity is >1024: {}", arity);
        }
        let atom = name.into_atom();

        let functor = unsafe { PL_new_functor(atom.atom_ptr(), arity.try_into().unwrap()) };

        unsafe { Functor::wrap(functor) }
    }

    /// Return the underlying `functor_t` which SWI-Prolog uses to refer to the functor.
    pub fn functor_ptr(&self) -> functor_t {
        self.functor
    }

    /// Retrieve the name of this functor as an atom and pass it into the given function.
    ///
    /// The atom does not outlive this call, and the reference count
    /// is never incremented. This may be slightly faster in some
    /// cases than returning the name directly.
    ///
    /// This will panic if no prolog engine is active on this thread.
    pub fn with_name<F, R>(&self, func: F) -> R
    where
        F: Fn(&Atom) -> R,
    {
        assert_some_engine_is_active();
        let atom = unsafe { Atom::wrap(PL_functor_name(self.functor)) };

        let result = func(&atom);

        std::mem::forget(atom);

        result
    }

    /// Retrieve the name of this functor as an atom.
    ///
    /// This will panic if no prolog engine is active on this thread.
    pub fn name(&self) -> Atom {
        self.with_name(|n| n.clone())
    }

    /// Retrieve the name of this functor as a string.
    ///
    /// This will panic if no prolog engine is active on this thread.
    pub fn name_string(&self) -> String {
        self.with_name(|n| n.name())
    }

    /// Retrieve the arity of this functor.
    ///
    /// This will panic if no prolog engine is active on this thread.
    pub fn arity(&self) -> u16 {
        assert_some_engine_is_active();
        let arity = unsafe { PL_functor_arity(self.functor) };

        arity.try_into().unwrap()
    }
}

unifiable! {
    (self: Functor, term) => {
        let result = unsafe {PL_unify_compound(term.term_ptr(), self.functor)};

        result != 0
    }
}

term_getable! {
    (Functor, "functor", term) => {
        let mut functor = 0;
        let result = unsafe { PL_get_functor(term.term_ptr(), &mut functor) };

        if result == 0 {
            None
        }
        else {
            Some(unsafe { Functor::wrap(functor) })
        }

    }
}

term_putable! {
    (self: Functor, term) => {
        unsafe {PL_put_functor(term.term_ptr(), self.functor)};
    }
}

/// A struct which provides a way to delay and cache functor creation.
///
/// This struct wraps a static string and an arity and uses it to
/// construct a swipl functor on the first invocation of
/// `as_functor`. Subsequent invocations will reuse the earlier
/// constructed functor.
///
/// The purpose of this struct is to back the implementation of the
/// `functor!` macro, but it's also usable on its own.
pub struct LazyFunctor {
    name: &'static str,
    arity: u16,
    f: AtomicUsize,
}

impl LazyFunctor {
    /// Create a new LazyFunctor.
    ///
    /// This constructor is const, as all it does is set up the
    /// struct. No actual calls into SWI-Prolog happen at this stage.
    pub const fn new(name: &'static str, arity: u16) -> Self {
        Self {
            name,
            arity,
            f: AtomicUsize::new(0),
        }
    }

    /// Create a functor, or return an earlier created functor.
    ///
    /// On first call, this will call swipl to create a
    /// functor. Subsequent calls will reuse the functor that was
    /// retrieved before.
    pub fn as_functor(&self) -> Functor {
        let ptr = self.f.load(Ordering::Relaxed);
        if ptr == 0 {
            // we've not yet allocated a functor. let's do it now.
            let functor = Functor::new(self.name, self.arity);

            self.f
                .store(functor.functor_ptr() as atom_t, Ordering::Relaxed);
            // Note that no special precautions have to be taken
            // around refcounting and garbage collection. Unlike
            // atoms, functors are not refcounted and are valid for
            // the entire prolog session.

            functor
        } else {
            let functor = unsafe { Functor::wrap(ptr as functor_t) };

            functor
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::*;

    #[test]
    fn create_and_query_functor() {
        let engine = Engine::new();
        let _activation = engine.activate();

        let f = Functor::new("moocows", 3);

        assert_eq!("moocows", f.name_string());
        assert_eq!("moocows", f.name().name());
        f.with_name(|name| assert_eq!("moocows", name.name()));

        assert_eq!(3, f.arity());
    }

    #[test]
    fn unify_same_functor_twice_succeeds() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let f = Functor::new("moocows", 3);
        let term = context.new_term_ref();
        assert!(term.unify(&f).is_ok());
        assert!(term.unify(&f).is_ok());
    }

    #[test]
    fn unity_retrieve_same_functor() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let f = Functor::new("moocows", 3);
        let term = context.new_term_ref();
        assert!(term.unify(&f).is_ok());
    }

    #[test]
    fn unify_different_functor_arity_fails() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let f1 = Functor::new("moocows", 3);
        let term = context.new_term_ref();
        term.unify(&f1).unwrap();
        let f2: Functor = term.get().unwrap();
        assert_eq!(f1, f2);
    }

    #[test]
    fn unify_different_functor_name_fails() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let f1 = Functor::new("moocows", 3);
        let f2 = Functor::new("oinkpigs", 3);
        let term = context.new_term_ref();
        assert!(term.unify(&f1).is_ok());
        assert!(!term.unify(&f2).is_ok());
    }

    #[test]
    #[should_panic]
    fn functor_creation_with_too_high_arity_panics() {
        let engine = Engine::new();
        let _activation = engine.activate();

        let _f = Functor::new("moocows", 1025);
    }

    #[test]
    fn functor_arg_unify_and_get_succeeds() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let f = Functor::new("moocows", 2);
        let term = context.new_term_ref();
        assert!(term.get_arg::<u64>(1).unwrap_err().is_failure());
        assert!(term.unify(f).is_ok());
        assert!(term.get_arg::<u64>(1).unwrap_err().is_failure());
        assert!(term.unify_arg(1, 42_u64).is_ok());
        assert_eq!(42_u64, term.get_arg(1).unwrap());
        assert!(term.unify_arg(1, 42_u64).is_ok());
        assert!(!term.unify_arg(1, 43_u64).is_ok());

        assert!(term.unify_arg(2, 24_u64).is_ok());
        assert_eq!(24_u64, term.get_arg(2).unwrap());

        assert!(!term.unify_arg(3, 24_u64).is_ok());
        assert!(term.get_arg::<u64>(3).unwrap_err().is_failure());
    }

    #[test]
    fn lazy_functor_to_functor() {
        let engine = Engine::new();
        let _activation = engine.activate();

        let lazy = LazyFunctor::new("foo", 1);
        let f1 = lazy.as_functor();
        let f2 = lazy.as_functor();
        let f3 = Functor::new("foo", 1);

        assert_eq!(f1, f2);
        assert_eq!(f1, f3);
    }

    use swipl_macros::{atom, functor};
    #[test]
    fn inline_functor_through_macro_allstring() {
        let engine = Engine::new();
        let _activation = engine.activate();

        let f = functor!("foo/3");

        assert_eq!(atom!("foo"), f.name());
        assert_eq!(3, f.arity());
    }

    #[test]
    fn inline_functor_through_macro_string_comma() {
        let engine = Engine::new();
        let _activation = engine.activate();

        let f = functor!("foo", 3);

        assert_eq!(atom!("foo"), f.name());
        assert_eq!(3, f.arity());
    }

    #[test]
    fn inline_functor_through_macro_string_slash() {
        let engine = Engine::new();
        let _activation = engine.activate();

        let f = functor!("foo" / 3);

        assert_eq!(atom!("foo"), f.name());
        assert_eq!(3, f.arity());
    }

    #[test]
    fn inline_functor_through_macro_ident_comma() {
        let engine = Engine::new();
        let _activation = engine.activate();

        let f = functor!(foo, 3);

        assert_eq!(atom!("foo"), f.name());
        assert_eq!(3, f.arity());
    }

    #[test]
    fn inline_functor_through_macro_ident_slash() {
        let engine = Engine::new();
        let _activation = engine.activate();

        let f = functor!(foo / 3);

        assert_eq!(atom!("foo"), f.name());
        assert_eq!(3, f.arity());
    }
}
