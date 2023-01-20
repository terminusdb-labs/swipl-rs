//! Prolog predicates.
//!
//! A prolog predicate is a core datatype in prolog. It is a
//! combination of a functor and a module. Just like functors and
//! modules, predicates are not reference-counted and are never
//! garbage collected.
//!
//! This module provides functors and types for intearcting with
//! prolog predicates.
use std::convert::TryInto;

use super::atom::*;
use super::engine::*;
use super::fli::*;
use super::functor::*;
use super::module::*;

/// A wrapper for a prolog predicate.
#[derive(Clone, Copy)]
pub struct Predicate {
    predicate: predicate_t,
}

// a `predicate_t` is a pointer which is normally not send or
// sync. SWI-Prolog however guarantees that this pointer will remain
// valid.
unsafe impl Send for Predicate {}
unsafe impl Sync for Predicate {}

impl Predicate {
    /// Wrap a `predicate_t`, which is how the SWI-Prolog fli represents predicates.
    ///
    /// # Safety
    /// This is unsafe because no check is done to ensure that the
    /// predicate_t indeed points at a valid predicate. The caller
    /// will have to ensure that this is the case.
    pub unsafe fn wrap(predicate: predicate_t) -> Self {
        Self { predicate }
    }

    /// Create a new predicate from the given functor and module.
    ///
    /// This will panic if no prolog engine is active on this thread.
    pub fn new(functor: Functor, module: Module) -> Self {
        assert_some_engine_is_active();
        let predicate = unsafe { PL_pred(functor.functor_ptr(), module.module_ptr()) };

        unsafe { Self::wrap(predicate) }
    }

    /// Return the underlying `predicate_t` which SWI-Prolog uses to refer to the predicate.
    pub fn predicate_ptr(&self) -> predicate_t {
        self.predicate
    }

    /// Retrieve the name of this predicate as an atom and pass it into the given function.
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
        let mut atom: atom_t = 0;
        unsafe {
            PL_predicate_info(
                self.predicate,
                &mut atom,
                std::ptr::null_mut(),
                std::ptr::null_mut(),
            );
        }
        let atom = unsafe { Atom::wrap(atom) };

        let result = func(&atom);

        std::mem::forget(atom);

        result
    }

    /// Retrieve the name of this predicate as an atom.
    ///
    /// This will panic if no prolog engine is active on this thread.
    pub fn name(&self) -> Atom {
        self.with_name(|n| n.clone())
    }

    /// Retrieve the name of this predicate as a string.
    ///
    /// This will panic if no prolog engine is active on this thread.
    pub fn name_string(&self) -> String {
        self.with_name(|n| n.name())
    }

    /// Retrieve the arity of this predicate.
    ///
    /// This will panic if no prolog engine is active on this thread.
    pub fn arity(&self) -> u16 {
        assert_some_engine_is_active();
        let mut arity = 0;
        unsafe {
            PL_predicate_info(
                self.predicate,
                std::ptr::null_mut(),
                &mut arity,
                std::ptr::null_mut(),
            );
        }

        arity.try_into().unwrap()
    }

    /// Retrieve the module of this predicate.
    ///
    /// this will panic if no prolog engine is active on this thread.
    pub fn module(&self) -> Module {
        assert_some_engine_is_active();
        let mut module: module_t = std::ptr::null_mut();
        unsafe {
            PL_predicate_info(
                self.predicate,
                std::ptr::null_mut(),
                std::ptr::null_mut(),
                &mut module,
            );

            Module::wrap(module)
        }
    }
}
