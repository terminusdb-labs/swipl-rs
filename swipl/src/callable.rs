use crate::context::*;
use crate::fli::*;
use crate::module::*;
use crate::result::*;
use crate::term::*;
use crate::predicate::*;
use thiserror::Error;

use std::convert::TryInto;

#[derive(Error, Debug)]
pub enum PredicateWrapError {
    #[error("predicate has arity {actual} but {expected} was required")]
    WrongArity{expected: u16, actual: u16}
}

#[derive(Clone, Copy)]
pub struct CallablePredicate<const N: usize> {
    predicate: predicate_t,
}

impl<const N: usize> CallablePredicate<N> {
    pub unsafe fn wrap(predicate: predicate_t) -> Self {
        // no check for arity or if the predicate even exists!
        Self { predicate }
    }

    pub fn new<P: ActiveEnginePromise>(predicate: &Predicate, promise: &P) -> Result<Self, PredicateWrapError> {
        let arity = predicate.arity(promise);
        if arity as usize != N {
            Err(PredicateWrapError::WrongArity{expected: N as u16, actual: arity})
        }
        else {
            Ok(unsafe { Self::wrap(predicate.predicate_ptr()) })
        }
    }
}

pub trait Callable<const N: usize> {
    type ContextType: OpenCallable;

    fn open<'a, C: ContextType>(
        self,
        context: &'a Context<C>,
        module: Option<&Module>,
        args: [&Term; N],
    ) -> Context<'a, Self::ContextType>;
}

pub struct OpenPredicate {
    qid: qid_t,
    closed: bool,
}

pub unsafe trait OpenCallable: Sized {
    fn next_solution<'a>(this: &Context<'a, Self>) -> PrologResult<bool>;
    fn cut<'a>(this: Context<'a, Self>);
    fn discard<'a>(this: Context<'a, Self>);
}

impl<'a, C: OpenCallable> Context<'a, C> {
    pub fn next_solution(&self) -> PrologResult<bool> {
        C::next_solution(self)
    }

    pub fn cut(self) {
        C::cut(self)
    }

    pub fn discard(self) {
        C::discard(self)
    }
}

unsafe impl<T: OpenCallable> ContextType for T {}

unsafe impl OpenCallable for OpenPredicate {
    fn next_solution<'a>(this: &Context<'a, Self>) -> PrologResult<bool> {
        this.assert_activated();
        let result = unsafe { PL_next_solution(this.context.qid) };
        match result {
            -1 => {
                let exception = unsafe { PL_exception(this.context.qid) };
                // rethrow this exception but as the special 0 exception which remains alive
                unsafe { PL_raise_exception(exception) };

                Err(PrologError::Exception)
            }
            0 => Err(PrologError::Failure),
            1 => Ok(false),
            2 => Ok(true),
            _ => panic!("unknown query result type {}", result),
        }
    }

    fn cut<'a>(mut this: Context<'a, Self>) {
        this.assert_activated();
        // TODO handle exceptions

        unsafe { PL_cut_query(this.context.qid) };
        this.context.closed = true;
    }

    fn discard<'a>(mut this: Context<'a, Self>) {
        this.assert_activated();
        // TODO handle exceptions

        unsafe { PL_close_query(this.context.qid) };
        this.context.closed = true;
    }
}

impl<const N: usize> Callable<N> for CallablePredicate<N> {
    type ContextType = OpenPredicate;

    fn open<'a, C: ContextType>(
        self,
        context: &'a Context<C>,
        module: Option<&Module>,
        args: [&Term; N],
    ) -> Context<'a, Self::ContextType> {
        context.assert_activated();
        context.assert_no_exception();
        let module_context = module
            .map(|c| c.module_ptr())
            .unwrap_or(std::ptr::null_mut());
        let flags = PL_Q_NORMAL | PL_Q_CATCH_EXCEPTION | PL_Q_EXT_STATUS;
        unsafe {
            let terms = PL_new_term_refs(N as i32);
            for i in 0..args.len() {
                let term = context.wrap_term_ref(terms + i);
                assert!(term.unify(args[i]).is_ok());
            }

            let qid = PL_open_query(
                module_context,
                flags.try_into().unwrap(),
                self.predicate,
                terms,
            );

            let query = OpenPredicate { qid, closed: false };

            context.deactivate();
            Context::new_activated(Some(context), query, context.engine_ptr())
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::prelude::*;
    #[test]
    fn call_prolog_inline() -> PrologResult<()> {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = term! {context: flurps(flargh)}?;
        context.call_once(pred!(writeq / 1), [&term]).unwrap();
        context.call_once(pred!(nl / 0), []).unwrap();

        Ok(())
    }
}
