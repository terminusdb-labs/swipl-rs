//! Prolog contexts.
//!
//!
use super::atom::*;
use super::callable::*;
use super::engine::*;
use super::fli::*;
use super::functor::*;
use super::module::*;
use super::predicate::*;
use super::result::*;
use super::term::*;

use std::cell::Cell;

use swipl_macros::{prolog, term};

pub unsafe fn with_cleared_exception<R>(f: impl FnOnce() -> R) -> R {
    let error_term_ref = PL_exception(0);
    if error_term_ref != 0 {
        let backup_term_ref = PL_new_term_ref();
        assert!(PL_unify(backup_term_ref, error_term_ref) != 0);
        PL_clear_exception();
        let result = f();
        PL_raise_exception(backup_term_ref);
        PL_reset_term_refs(backup_term_ref);

        result
    } else {
        f()
    }
}

pub struct ExceptionTerm<'a>(Term<'a>);

impl<'a> ExceptionTerm<'a> {
    pub fn clear_exception(self) {
        self.assert_term_handling_possible();

        unsafe { PL_clear_exception() }
    }

    /// Call the given function with a copy of the exception term in a context where the exception has been cleared.
    /// This function is marked unsafe because it is not safe to use the original ExceptionTerm from within the given function.
    pub unsafe fn with_cleared_exception<'b, C: ContextType, R>(
        &'b self,
        ctx: &'b Context<C>,
        f: impl FnOnce(&Term) -> R,
    ) -> R {
        ctx.assert_activated();
        let backup_term_ref = PL_new_term_ref();
        assert!(PL_unify(backup_term_ref, self.0.term_ptr()) != 0);
        let backup_term = Term::new(backup_term_ref, ctx);
        PL_clear_exception();

        // should we handle panics?
        let result = f(&backup_term);

        PL_raise_exception(backup_term_ref);

        backup_term.reset();

        result
    }
}

impl<'a> std::ops::Deref for ExceptionTerm<'a> {
    type Target = Term<'a>;
    fn deref(&self) -> &Term<'a> {
        &self.0
    }
}

pub struct Context<'a, T: ContextType> {
    parent: Option<&'a dyn ContextParent>,
    pub context: T,
    engine: PL_engine_t,
    activated: Cell<bool>,
    exception_handling: Cell<bool>,
}

impl<'a, T: ContextType> Context<'a, T> {
    pub unsafe fn new_activated(
        parent: Option<&'a dyn ContextParent>,
        context: T,
        engine: PL_engine_t,
    ) -> Self {
        Context {
            parent: parent,
            context,
            engine,
            activated: Cell::new(true),
            exception_handling: Cell::new(false),
        }
    }

    pub unsafe fn deactivate(&self) {
        self.activated.set(false)
    }

    pub fn assert_activated(&self) {
        if !self.activated.get() {
            panic!("tried to use inactive context");
        }
    }

    pub fn assert_no_exception(&self) {
        if self.has_exception() {
            panic!("tried to use context which has raised an exception");
        }
    }

    pub fn engine_ptr(&self) -> PL_engine_t {
        self.engine
    }

    pub unsafe fn wrap_term_ref(&self, term: term_t) -> Term {
        self.assert_activated();
        Term::new(term, self)
    }

    pub fn raise_exception<R>(&self, term: &Term) -> PrologResult<R>
    where
        T: FrameableContextType,
    {
        self.assert_activated();
        if term.is_var() {
            let frame = self.open_frame();
            let err = term! {frame: error(rust_error(raise_exception_called_with_variable), _)}?;
            unsafe {
                PL_raise_exception(err.term_ptr());
                PL_reset_term_refs(err.term_ptr());
            }
        } else {
            unsafe {
                PL_raise_exception(term.term_ptr());
            }
        }

        Err(PrologError::Exception)
    }

    pub fn has_exception(&self) -> bool {
        self.assert_activated();

        unsafe { PL_exception(0) != 0 }
    }

    pub fn clear_exception(&self) {
        self.with_uncleared_exception(|e| match e {
            None => (),
            Some(e) => e.clear_exception(),
        })
    }

    pub fn with_uncleared_exception<'b, R>(
        &'b self,
        f: impl FnOnce(Option<ExceptionTerm<'b>>) -> R,
    ) -> R {
        self.assert_activated();
        if self.exception_handling.replace(true) {
            panic!("re-entered exception handler");
        }

        let exception = unsafe { PL_exception(0) };
        let arg = match exception == 0 {
            true => None,
            false => {
                let term = unsafe { self.wrap_term_ref(exception) };
                Some(ExceptionTerm(term))
            }
        };

        // TODO should we take panics into account when clearing exception handling status?
        let result = f(arg);

        self.exception_handling.set(false);

        result
    }

    pub fn with_exception<'b, R>(&'b self, f: impl FnOnce(Option<&Term>) -> R) -> R {
        self.with_uncleared_exception(|e| match e {
            None => f(None),
            Some(e) => unsafe { e.with_cleared_exception(self, |e| f(Some(e))) },
        })
    }

    pub fn catch<R>(
        &self,
        result: PrologResult<R>,
        handler: impl Fn(&Term) -> PrologResult<R>,
    ) -> PrologResult<R> {
        match result {
            Err(PrologError::Exception) => self.with_exception(move |term| {
                handler(term.expect("expected exception term due to exception result"))
            }),
            _ => result,
        }
    }
}

pub trait ContextParent {
    fn reactivate(&self);
    fn as_term_origin(&self) -> &dyn TermOrigin;
}

impl<'a, T: ContextType> ContextParent for Context<'a, T> {
    fn reactivate(&self) {
        if self.activated.replace(true) {
            panic!("context already active");
        }
    }

    fn as_term_origin(&self) -> &dyn TermOrigin {
        self
    }
}

impl<'a, T: ContextType> TermOrigin for Context<'a, T> {
    fn is_engine_active(&self) -> bool {
        // unsafe justification: We have an active context, therefore
        // SWI-Prolog should have been initialized, which makes this
        // call safe.
        is_engine_active(self.engine)
    }

    fn origin_engine_ptr(&self) -> PL_engine_t {
        self.engine
    }
}

impl<'a, T: ContextType> Drop for Context<'a, T> {
    fn drop(&mut self) {
        if let Some(parent) = self.parent {
            parent.reactivate();
        }
    }
}

pub unsafe trait ContextType {}

pub struct ActivatedEngine<'a> {
    _activation: EngineActivation<'a>,
}

impl<'a> Into<Context<'a, ActivatedEngine<'a>>> for EngineActivation<'a> {
    fn into(self) -> Context<'a, ActivatedEngine<'a>> {
        let engine = self.engine_ptr();
        let context = ActivatedEngine { _activation: self };

        unsafe { Context::new_activated(None, context, engine) }
    }
}

unsafe impl<'a> ContextType for ActivatedEngine<'a> {}

pub struct UnmanagedContext {
    // only here to prevent automatic construction
    _x: (),
}
unsafe impl ContextType for UnmanagedContext {}

// This is unsafe to call if we are not in a swipl environment, or if some other context is active. Furthermore, the lifetime will most definitely be wrong. This should be used by code that doesn't promiscuously spread this context. all further accesses should be through borrows.
pub unsafe fn unmanaged_engine_context() -> Context<'static, UnmanagedContext> {
    let current = current_engine_ptr();

    if current.is_null() {
        panic!("tried to create an unmanaged engine context, but no engine is active");
    }

    Context::new_activated(None, UnmanagedContext { _x: () }, current)
}

enum FrameState {
    Active,
    Closed,
}

pub struct Frame {
    fid: PL_fid_t,
    state: FrameState,
}

unsafe impl ContextType for Frame {}

impl Drop for Frame {
    fn drop(&mut self) {
        match &self.state {
            FrameState::Active =>
            // unsafe justification: all instantiations of Frame happen in
            // this module.  This module only instantiates the frame as
            // part of the context mechanism. No 'free' Frames are ever
            // returned.  This mechanism ensures that the frame is only
            // discarded if there's no inner frame still
            // remaining. It'll also ensure that the engine of the
            // frame is active while dropping.
            unsafe { PL_discard_foreign_frame(self.fid) }
            _ => {}
        }
    }
}

impl<'a> Context<'a, Frame> {
    pub fn close_frame(mut self) {
        self.context.state = FrameState::Closed;
        // unsafe justification: reasons for safety are the same as in a normal drop. Also, since we just set framestate to discarded, the drop won't try to subsequently close this same frame.
        unsafe { PL_close_foreign_frame(self.context.fid) };
    }

    pub fn discard_frame(self) {
        // would happen automatically but might as well be explicit
        std::mem::drop(self)
    }

    pub fn rewind_frame(&self) {
        self.assert_activated();
        // unsafe justification: We just checked that this frame right here is currently the active context. Therefore it can be rewinded.
        unsafe { PL_rewind_foreign_frame(self.context.fid) };
    }
}

pub unsafe trait FrameableContextType: ContextType {}
unsafe impl FrameableContextType for UnmanagedContext {}
unsafe impl<'a> FrameableContextType for ActivatedEngine<'a> {}
unsafe impl FrameableContextType for Frame {}

impl<'a, C: FrameableContextType> Context<'a, C> {
    pub fn open_frame(&self) -> Context<Frame> {
        self.assert_activated();
        let fid = unsafe { PL_open_foreign_frame() };

        let frame = Frame {
            fid,
            state: FrameState::Active,
        };

        self.activated.set(false);
        unsafe { Context::new_activated(Some(self), frame, self.engine) }
    }
}

pub unsafe trait ActiveEnginePromise: Sized {
    fn new_atom(&self, name: &str) -> Atom {
        Atom::new(name)
    }

    fn new_functor<A: IntoAtom>(&self, name: A, arity: u16) -> Functor {
        Functor::new(name, arity)
    }

    fn new_module<A: IntoAtom>(&self, name: A) -> Module {
        Module::new(name)
    }

    fn new_predicate(&self, functor: &Functor, module: &Module) -> Predicate {
        Predicate::new(functor, module)
    }
}

unsafe impl<'a> ActiveEnginePromise for EngineActivation<'a> {}
unsafe impl<'a, C: ContextType> ActiveEnginePromise for Context<'a, C> {}
unsafe impl<'a> ActiveEnginePromise for &'a dyn TermOrigin {}

pub struct UnsafeActiveEnginePromise {
    _x: bool,
}

impl UnsafeActiveEnginePromise {
    pub unsafe fn new() -> Self {
        Self { _x: false }
    }
}

unsafe impl ActiveEnginePromise for UnsafeActiveEnginePromise {}

pub unsafe trait QueryableContextType: FrameableContextType {}
unsafe impl QueryableContextType for UnmanagedContext {}
unsafe impl<'a> QueryableContextType for ActivatedEngine<'a> {}
unsafe impl QueryableContextType for Frame {}

prolog! {
    #[module("user")]
    fn read_term_from_atom(atom_term, result, options);
    #[module("user")]
    #[name("call")]
    pub fn open_call(term);
}

impl<'a, T: QueryableContextType> Context<'a, T> {
    pub fn new_term_ref(&self) -> Term {
        self.assert_activated();
        unsafe {
            let term = PL_new_term_ref();
            Term::new(term, self)
        }
    }

    pub fn open<C: Callable<N>, const N: usize>(
        &self,
        callable: C,
        args: [&Term; N],
    ) -> Context<C::ContextType> {
        callable.open(self, None, args)
    }

    pub fn call_once<C: Callable<N>, const N: usize>(
        &self,
        callable: C,
        args: [&Term; N],
    ) -> PrologResult<()> {
        let query = callable.open(self, None, args);
        query.next_solution()?;
        query.cut();

        Ok(())
    }

    pub fn open_with_module<C: Callable<N>, const N: usize>(
        &self,
        callable: C,
        module: Option<&Module>,
        args: [&Term; N],
    ) -> Context<C::ContextType> {
        callable.open(self, module, args)
    }

    pub fn term_from_string(&self, s: &str) -> PrologResult<Term> {
        let term = self.new_term_ref();
        let frame = self.open_frame();

        let arg1 = frame.new_term_ref();
        let arg3 = frame.new_term_ref();

        assert!(arg1.unify(s).is_ok());
        assert!(arg3.unify(Nil).is_ok());

        read_term_from_atom(&frame, &arg1, &term, &arg3).once()?;
        frame.close_frame();

        Ok(term)
    }

    pub fn open_call(&'a self, t: &Term<'a>) -> Context<'a, impl OpenCallable> {
        open_call(self, t)
    }

    pub fn exception<'b>(&'b self) -> Option<Term<'b>> {
        self.assert_activated();

        let exception = unsafe { PL_exception(0) };
        if exception != 0 {
            let exception_term = unsafe { Term::new(exception, self) };
            let return_term = self.new_term_ref();
            return_term.unify(exception_term).unwrap();
            Some(return_term)
        } else {
            None
        }
    }

    pub fn try_or_die<R, E: IntoPrologException>(&self, r: Result<R, E>) -> PrologResult<R> {
        match r {
            Ok(ok) => Ok(ok),
            Err(e) => {
                let reset_term = self.new_term_ref();
                let exception_term = e.into_prolog_exception(self)?;
                let result = self.raise_exception(&exception_term);

                unsafe {
                    reset_term.reset();
                }

                result
            }
        }
    }
}

pub trait IntoPrologException {
    fn into_prolog_exception<'a, 'b, T: QueryableContextType>(
        self,
        context: &'a Context<'b, T>,
    ) -> PrologResult<Term<'a>>;
}

impl IntoPrologException for std::io::Error {
    fn into_prolog_exception<'a, 'b, T: QueryableContextType>(
        self,
        context: &'a Context<'b, T>,
    ) -> PrologResult<Term<'a>> {
        let msg = format!("{}", self);
        term! {context: error(rust_io_error(#msg))}
    }
}

pub unsafe fn prolog_catch_unwind<F: FnOnce() -> R + std::panic::UnwindSafe, R>(
    f: F,
) -> PrologResult<R> {
    let result = std::panic::catch_unwind(f);
    match result {
        Ok(result) => Ok(result),
        Err(panic) => {
            let context = unmanaged_engine_context();
            let panic_term = context.new_term_ref();
            let error_term = term! {context: error(rust_error(panic(#&panic_term)), _)}?;

            match panic.downcast_ref::<&str>() {
                Some(panic_msg) => {
                    panic_term.unify(panic_msg).unwrap();
                }
                None => match panic.downcast_ref::<String>() {
                    Some(panic_msg) => {
                        panic_term.unify(panic_msg.as_str()).unwrap();
                    }
                    None => {
                        panic_term.unify("unknown panic type").unwrap();
                    }
                },
            }

            context.raise_exception::<()>(&error_term).unwrap_err();
            Err(PrologError::Exception)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::predicates;

    #[test]
    fn get_term_ref_on_fresh_engine() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let _term = context.new_term_ref();
    }

    #[test]
    fn get_term_ref_on_frame() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context1: Context<_> = activation.into();
        let _term1 = context1.new_term_ref();

        let context2 = context1.open_frame();
        let _term2 = context2.new_term_ref();
        std::mem::drop(context2);
        let _term3 = context1.new_term_ref();
    }

    #[test]
    #[should_panic]
    fn get_term_ref_from_inactive_context_panics() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context1: Context<_> = activation.into();
        let _context2 = context1.open_frame();

        let _term = context1.new_term_ref();
    }

    #[test]
    fn query_det() -> PrologResult<()> {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let functor_is = context.new_functor("is", 2);
        let functor_plus = context.new_functor("+", 2);
        let module = context.new_module("user");
        let predicate = context.new_predicate(&functor_is, &module);
        let callable = CallablePredicate::new(&predicate).unwrap();

        let term1 = context.new_term_ref();
        let term2 = context.new_term_ref();

        term2.unify(&functor_plus)?;
        term2.unify_arg(1, 40_u64)?;
        term2.unify_arg(2, 2_u64)?;

        let query = context.open(callable, [&term1, &term2]);
        let next = query.next_solution()?;

        assert!(!next);
        assert_eq!(42_u64, term1.get()?);

        let next = query.next_solution();
        assert!(next.is_err());

        Ok(())
    }

    #[test]
    fn query_auto_discard() -> PrologResult<()> {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let functor_is = context.new_functor("is", 2);
        let functor_plus = context.new_functor("+", 2);
        let module = context.new_module("user");
        let predicate = context.new_predicate(&functor_is, &module);
        let callable = CallablePredicate::new(&predicate).unwrap();

        let term1 = context.new_term_ref();
        let term2 = context.new_term_ref();

        assert!(term2.unify(&functor_plus).is_ok());
        assert!(term2.unify_arg(1, 40_u64).is_ok());
        assert!(term2.unify_arg(2, 2_u64).is_ok());

        {
            let query = context.open(callable, [&term1, &term2]);
            let next = query.next_solution()?;

            assert!(!next);
            assert_eq!(42_u64, term1.get().unwrap());
        }

        // after leaving the block, we have discarded
        assert!(term1.get::<u64>().unwrap_err().is_failure());

        Ok(())
    }

    #[test]
    fn query_manual_discard() -> PrologResult<()> {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let functor_is = context.new_functor("is", 2);
        let functor_plus = context.new_functor("+", 2);
        let module = context.new_module("user");
        let predicate = context.new_predicate(&functor_is, &module);
        let callable = CallablePredicate::new(&predicate).unwrap();

        let term1 = context.new_term_ref();
        let term2 = context.new_term_ref();

        term2.unify(&functor_plus)?;
        term2.unify_arg(1, 40_u64)?;
        term2.unify_arg(2, 2_u64)?;

        {
            let query = context.open(callable, [&term1, &term2]);
            let next = query.next_solution()?;

            assert!(!next);
            assert_eq!(42_u64, term1.get()?);
            query.discard();
        }

        // after leaving the block, we have discarded
        assert!(term1.get::<u64>().unwrap_err().is_failure());

        Ok(())
    }

    #[test]
    fn query_cut() -> PrologResult<()> {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let functor_is = context.new_functor("is", 2);
        let functor_plus = context.new_functor("+", 2);
        let module = context.new_module("user");
        let predicate = context.new_predicate(&functor_is, &module);
        let callable = CallablePredicate::new(&predicate).unwrap();

        let term1 = context.new_term_ref();
        let term2 = context.new_term_ref();

        term2.unify(&functor_plus)?;
        term2.unify_arg(1, 40_u64)?;
        term2.unify_arg(2, 2_u64)?;

        {
            let query = context.open(callable, [&term1, &term2]);
            let next = query.next_solution()?;

            assert!(!next);
            assert_eq!(42_u64, term1.get()?);
            query.cut();
        }

        // a cut query leaves data intact
        assert_eq!(42_u64, term1.get()?);

        Ok(())
    }

    #[test]
    fn term_from_string_works() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.term_from_string("foo(bar(baz,quux))").unwrap();
        let functor_foo = context.new_functor("foo", 1);
        let functor_bar = context.new_functor("bar", 2);

        assert_eq!(functor_foo, term.get().unwrap());
        assert_eq!(functor_bar, term.get_arg(1).unwrap());
    }

    #[test]
    fn open_call_nondet() -> PrologResult<()> {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.term_from_string("member(X, [a,b,c])").unwrap();
        let term_x = context.new_term_ref();
        assert!(term.unify_arg(1, &term_x).is_ok());

        let query = context.open_call(&term);
        assert!(query.next_solution()?);
        term_x.get_atomable(|a| assert_eq!("a", a.unwrap().name()))?;

        assert!(query.next_solution()?);
        term_x.get_atomable(|a| assert_eq!("b", a.unwrap().name()))?;

        assert!(!query.next_solution()?);
        term_x.get_atomable(|a| assert_eq!("c", a.unwrap().name()))?;

        assert!(query.next_solution().unwrap_err().is_failure());

        Ok(())
    }

    #[test]
    fn open_query_with_0_arg_predicate() -> PrologResult<()> {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let functor = context.new_functor("true", 0);
        let module = context.new_module("user");
        let predicate = context.new_predicate(&functor, &module);
        let callable = CallablePredicate::new(&predicate).unwrap();

        let query = context.open(callable, []);
        assert!(!query.next_solution()?);

        Ok(())
    }

    #[test]
    fn freeze_exception_is_delayed_until_next_query() -> PrologResult<()> {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.term_from_string("freeze(X, throw(foo))")?;
        let term_x = context.new_term_ref();
        term.unify_arg(1, &term_x)?;
        let query = context.open_call(&term);
        assert!(!query.next_solution()?);
        query.cut();

        assert!(term_x.unify(42_u64).is_ok());

        let term = context.new_term_ref();
        term.unify(true)?;
        let query = context.open_call(&term);
        let next = query.next_solution();
        assert!(next.unwrap_err().is_exception());
        query.with_exception(|e| {
            let exception_term = e.unwrap();
            let atomable: Atomable = exception_term.get().unwrap();
            assert_eq!("foo", atomable.name());

            assert!(term.get::<u64>().unwrap_err().is_failure());
        });

        Ok(())
    }

    prolog! {
        #[name("is")]
        fn prolog_arithmetic(term, e);
    }

    #[test]
    #[should_panic(expected = "tried to use context which has raised an exception")]
    fn call_prolog_with_raised_exception_panics() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = context.new_term_ref();
        let term2 = context.new_term_ref();

        let query = prolog_arithmetic(&context, &term1, &term2);
        assert!(query.next_solution().unwrap_err().is_exception());
        assert!(query.has_exception());
        query.discard();
        let _query2 = prolog_arithmetic(&context, &term1, &term2);
    }

    predicates! {
        semidet fn unify_with_42(_context, term) {
            term.unify(42_u64)
        }
    }

    #[test]
    fn register_foreign_predicate() -> PrologResult<()> {
        let engine = Engine::new();
        let activation = engine.activate();

        assert!(register_unify_with_42());

        let context: Context<_> = activation.into();
        let term = context.new_term_ref();

        let functor = context.new_functor("unify_with_42", 1);
        let module = context.new_module("user");
        let predicate = context.new_predicate(&functor, &module);
        let callable = CallablePredicate::new(&predicate).unwrap();

        let query = context.open(callable, [&term]);
        assert!(!query.next_solution()?);
        assert_eq!(42, term.get::<u64>().unwrap());

        Ok(())
    }

    #[test]
    fn call_prolog_from_generated_rust_query_opener() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.new_term_ref();
        let expr = context.term_from_string("2+2").unwrap();

        let q = prolog_arithmetic(&context, &term, &expr);
        assert!(q.next_solution().is_ok());
        assert_eq!(4, term.get::<u64>().unwrap());
    }
}
