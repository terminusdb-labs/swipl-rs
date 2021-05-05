use std::convert::TryInto;

use super::engine::*;
use super::fli::*;
use super::functor::*;
use super::module::*;

pub struct Predicate {
    predicate: predicate_t,
}

impl Predicate {
    pub unsafe fn wrap(predicate: predicate_t) -> Self {
        Self { predicate }
    }

    pub fn new(functor: &Functor, module: &Module) -> Self {
        assert_some_engine_is_active();
        let predicate = unsafe { PL_pred(functor.functor_ptr(), module.module_ptr()) };

        unsafe { Self::wrap(predicate) }
    }

    pub fn predicate_ptr(&self) -> predicate_t {
        self.predicate
    }

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
}
