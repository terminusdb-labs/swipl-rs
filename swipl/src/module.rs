use super::atom::*;
use super::engine::*;
use super::fli::*;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Module {
    module: module_t,
}

impl Module {
    pub unsafe fn wrap(module: module_t) -> Self {
        Self { module }
    }

    pub fn new<A: IntoAtom>(name: A) -> Self {
        assert_some_engine_is_active();
        let atom = name.into_atom();
        unsafe { Self::wrap(PL_new_module(atom.atom_ptr())) }
    }

    pub fn module_ptr(&self) -> module_t {
        self.module
    }

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

    pub fn name(&self) -> Atom {
        self.with_name(|n| n.clone())
    }

    pub fn name_string(&self) -> String {
        self.with_name(|n| n.name().to_string())
    }

    pub fn with_name_string<F, R>(&self, func: F) -> R
    where
        F: Fn(&str) -> R,
    {
        self.with_name(|n| func(n.name()))
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
