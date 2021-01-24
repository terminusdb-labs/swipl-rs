use swipl_sys::*;

use super::functor::*;
use super::module::*;

pub struct Predicate {
    predicate: predicate_t,
}

impl Predicate {
    pub unsafe fn wrap(predicate: predicate_t) -> Self {
        Self { predicate }
    }

    pub unsafe fn new(functor: Functor, module: Module) -> Self {
        let predicate = PL_pred(functor.functor_ptr(), module.module_ptr());

        Self::wrap(predicate)
    }

    pub fn predicate_ptr(&self) -> predicate_t {
        self.predicate
    }
}
