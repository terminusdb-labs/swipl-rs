//! Prolog modules.
//!
//! Modules are prolog namespaces. They are created from an
//! atom. Unlike atoms, modules are not reference-counted and are
//! never garbage collected.
//!
//! This module provides functions and types for interacting with
//! prolog modules.
use super::atom::*;
use super::engine::*;
use super::fli::*;

/// A wrapped fora  prolog module.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Module {
    module: module_t,
}

// a `module_t` is a pointer which is normally not send or
// sync. SWI-Prolog however guarantees that this pointer will remain
// valid.
unsafe impl Send for Module {}
unsafe impl Sync for Module {}

impl Module {
    /// Wrap a `module_t`, which is how the SWI-Prolog fli represents modules.
    ///
    /// # Safety
    /// This is unsafe because no check is done to ensure that the
    /// module_t indeed points at a valid module. The caller will have
    /// to ensure that this is the case.
    pub unsafe fn wrap(module: module_t) -> Self {
        Self { module }
    }

    /// Create a new module from the given name.
    ///
    /// This will panic if no prolog engine is active on this thread.
    pub fn new<A: IntoAtom>(name: A) -> Self {
        assert_some_engine_is_active();
        let atom = name.into_atom();
        unsafe { Self::wrap(PL_new_module(atom.atom_ptr())) }
    }

    /// Return the underlying `module_t` which SWI-Prolog uses to refer to the module.
    pub fn module_ptr(&self) -> module_t {
        self.module
    }

    /// Retrieve the name of this module as an atom and pass it into the given function.
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
        let atom = unsafe { Atom::wrap(PL_module_name(self.module)) };

        let result = func(&atom);

        std::mem::forget(atom);

        result
    }

    /// Retrieve the name of this module as an atom.
    ///
    /// This will panic if no prolog engine is active on this thread.
    pub fn name(&self) -> Atom {
        self.with_name(|n| n.clone())
    }

    /// Retrieve the name of this module as a string.
    ///
    /// This will panic if no prolog engine is active on this thread.
    pub fn name_string(&self) -> String {
        self.with_name(|n| n.name())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_and_query_module() {
        let engine = Engine::new();
        let _activation = engine.activate();

        let module = Module::new("foo");
        assert_eq!("foo", module.name_string());
    }
}
