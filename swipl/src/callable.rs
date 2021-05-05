use crate::context::*;
use crate::engine::*;
use crate::fli::*;
use crate::functor::*;
use crate::module::*;
use crate::predicate::*;
use crate::result::*;
use crate::term::*;
use std::convert::TryInto;
use std::os::raw::c_void;
use std::sync::atomic::{AtomicPtr, Ordering};
use thiserror::Error;

pub struct LazyCallablePredicate<const N: usize> {
    module: Option<&'static str>,
    name: &'static str,
    predicate: AtomicPtr<c_void>,
}

impl<const N: usize> LazyCallablePredicate<N> {
    pub const fn new(module: Option<&'static str>, name: &'static str) -> Self {
        Self {
            module,
            name,
            predicate: AtomicPtr::new(std::ptr::null_mut()),
        }
    }

    pub fn as_callable(&self) -> CallablePredicate<N> {
        assert_some_engine_is_active();
        let mut loaded = self.predicate.load(Ordering::Relaxed);
        if loaded.is_null() {
            let functor = Functor::new(self.name, N as u16);
            let module_name = self.module.unwrap_or("");
            let module = Module::new(module_name);

            loaded = Predicate::new(&functor, &module).predicate_ptr();

            self.predicate
                .store(loaded, std::sync::atomic::Ordering::Relaxed);
        }

        unsafe { CallablePredicate::wrap(loaded) }
    }
}

impl<const N: usize> Callable<N> for LazyCallablePredicate<N> {
    type ContextType = OpenPredicate;

    fn open<'a, C: ContextType>(
        self,
        context: &'a Context<C>,
        module: Option<&Module>,
        args: [&Term; N],
    ) -> Context<'a, OpenPredicate> {
        self.as_callable().open(context, module, args)
    }
}

impl<'a, const N: usize> Callable<N> for &'a LazyCallablePredicate<N> {
    type ContextType = OpenPredicate;

    fn open<'b, C: ContextType>(
        self,
        context: &'b Context<C>,
        module: Option<&Module>,
        args: [&Term; N],
    ) -> Context<'b, OpenPredicate> {
        self.as_callable().open(context, module, args)
    }
}

#[derive(Error, Debug)]
pub enum PredicateWrapError {
    #[error("predicate has arity {actual} but {expected} was required")]
    WrongArity { expected: u16, actual: u16 },
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

    pub fn new(predicate: &Predicate) -> Result<Self, PredicateWrapError> {
        let arity = predicate.arity();
        if arity as usize != N {
            Err(PredicateWrapError::WrongArity {
                expected: N as u16,
                actual: arity,
            })
        } else {
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

    pub fn once(self) -> PrologResult<()> {
        self.next_solution()?;
        self.cut();

        Ok(())
    }

    pub fn ignore(self) -> PrologResult<()> {
        if let Err(PrologError::Exception) = self.next_solution() {
            Err(PrologError::Exception)
        } else {
            self.cut();

            Ok(())
        }
    }
}

unsafe impl<T: OpenCallable> ContextType for T {}
unsafe impl<T: OpenCallable> FrameableContextType for T {}

unsafe impl OpenCallable for OpenPredicate {
    fn next_solution<'a>(this: &Context<'a, Self>) -> PrologResult<bool> {
        println!("lets next solution");
        this.assert_activated();
        let result = unsafe { PL_next_solution(this.context.qid) };
        println!("result: {}", result);
        match result {
            -1 => {
                let exception = unsafe { PL_exception(this.context.qid) };
                // rethrow this exception but as the special 0 exception which remains alive
                unsafe { PL_raise_exception(exception) };

                Err(PrologError::Exception)
            }
            0 => Err(PrologError::Failure),
            1 => Ok(true),
            2 => Ok(false),
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

impl Drop for OpenPredicate {
    fn drop(&mut self) {
        if !self.closed {
            unsafe { PL_close_query(self.qid) };
        }
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
