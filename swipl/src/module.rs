use swipl_sys::*;

use super::atom::*;
use super::context::*;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Module {
    module: module_t,
}

impl Module {
    pub unsafe fn wrap(module: module_t) -> Self {
        Self { module }
    }

    pub unsafe fn new<A: IntoAtom>(name: A) -> Self {
        let atom = name.into_atom_unsafe();
        Self::wrap(PL_new_module(atom.atom_ptr()))
    }

    pub fn module_ptr(&self) -> module_t {
        self.module
    }

    pub fn with_name<P: ActiveEnginePromise, F, R>(&self, _: &P, func: F) -> R
    where
        F: Fn(&Atom) -> R,
    {
        let atom = unsafe { Atom::wrap(PL_module_name(self.module)) };

        let result = func(&atom);

        std::mem::forget(atom);

        result
    }

    pub fn name<P: ActiveEnginePromise>(&self, promise: &P) -> Atom {
        self.with_name(promise, |n| n.clone())
    }

    pub fn name_string<P: ActiveEnginePromise>(&self, promise: &P) -> String {
        self.with_name(promise, |n| n.name(promise).to_string())
    }

    pub fn with_name_string<P: ActiveEnginePromise, F, R>(&self, promise: &P, func: F) -> R
    where
        F: Fn(&str) -> R,
    {
        self.with_name(promise, |n| func(n.name(promise)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::*;

    #[test]
    fn create_and_query_module() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let module = context.new_module("foo");
        assert_eq!("foo", module.name_string(&context));
    }
}
