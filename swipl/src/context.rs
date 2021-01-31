use super::atom::*;
use super::consts::*;
use super::engine::*;
use super::functor::*;
use super::module::*;
use super::predicate::*;
use super::term::*;

use std::convert::TryInto;
use std::sync::atomic::{AtomicBool, Ordering};
use swipl_sys::*;

use swipl_macros::prolog;

use thiserror::Error;

pub struct Context<'a, T: ContextType> {
    parent: Option<&'a dyn ContextParent>,
    context: T,
    engine: PL_engine_t,
    activated: AtomicBool,
}

impl<'a, T: ContextType> Context<'a, T> {
    pub fn assert_activated(&self) {
        if !self.activated.load(Ordering::Relaxed) {
            panic!("tried to use inactive context");
        }
    }
    pub fn engine_ptr(&self) -> PL_engine_t {
        self.engine
    }
}

trait ContextParent {
    fn reactivate(&self);
}

impl<'a, T: ContextType> ContextParent for Context<'a, T> {
    fn reactivate(&self) {
        if self
            .activated
            .compare_and_swap(false, true, Ordering::Acquire)
        {
            panic!("context already active");
        }
    }
}

impl<'a, T: ContextType> TermOrigin for Context<'a, T> {
    fn is_engine_active(&self) -> bool {
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

        Context {
            parent: None,
            context,
            engine,
            activated: AtomicBool::new(true),
        }
    }
}

unsafe impl<'a> ContextType for ActivatedEngine<'a> {}

pub struct UnmanagedContext {
    // only here to prevent automatic construction
    _x: bool,
}
unsafe impl ContextType for UnmanagedContext {}

// This is unsafe to call if we are not in a swipl environment, or if some other context is active. Furthermore, the lifetime will most definitely be wrong. This should be used by code that doesn't promiscuously spread this context. all further accesses should be through borrows.
pub unsafe fn unmanaged_engine_context() -> Context<'static, UnmanagedContext> {
    let current = current_engine_ptr();

    if current.is_null() {
        panic!("tried to create an unmanaged engine context, but no engine is active");
    }

    Context {
        parent: None,
        context: UnmanagedContext { _x: false },
        engine: current,
        activated: AtomicBool::new(true),
    }
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
unsafe impl FrameableContextType for Query {}

impl<'a, C: FrameableContextType> Context<'a, C> {
    pub unsafe fn wrap_term_ref(&self, term: term_t) -> Term {
        self.assert_activated();
        Term::new(term, self)
    }

    pub fn open_frame(&self) -> Context<Frame> {
        self.assert_activated();
        let fid = unsafe { PL_open_foreign_frame() };

        let frame = Frame {
            fid,
            state: FrameState::Active,
        };

        self.activated.store(false, Ordering::Relaxed);
        Context {
            parent: Some(self),
            context: frame,
            engine: self.engine,
            activated: AtomicBool::new(true),
        }
    }
}

pub unsafe trait ActiveEnginePromise: Sized {
    fn new_atom(&self, name: &str) -> Atom {
        unsafe { Atom::new(name) }
    }

    fn new_functor<A: IntoAtom>(&self, name: A, arity: u16) -> Functor {
        if arity as usize > MAX_ARITY {
            panic!("functor arity is >1024: {}", arity);
        }
        let atom = name.into_atom(self);

        let functor = unsafe { PL_new_functor(atom.atom_ptr(), arity.try_into().unwrap()) };

        unsafe { Functor::wrap(functor) }
    }

    fn new_module<A: IntoAtom>(&self, name: A) -> Module {
        unsafe { Module::new(name) }
    }

    fn new_predicate(&self, functor: &Functor, module: &Module) -> Predicate {
        unsafe { Predicate::new(functor, module) }
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

pub struct Query {
    qid: qid_t,
    closed: bool,
}

unsafe impl ContextType for Query {}

pub unsafe trait QueryableContextType: FrameableContextType {}
unsafe impl QueryableContextType for UnmanagedContext {}
unsafe impl<'a> QueryableContextType for ActivatedEngine<'a> {}
unsafe impl QueryableContextType for Frame {}

prolog! {
    fn read_term_from_atom(atom_term, result, options);
}

impl<'a, T: QueryableContextType> Context<'a, T> {
    pub fn new_term_ref(&self) -> Term {
        self.assert_activated();
        unsafe {
            let term = PL_new_term_ref();
            Term::new(term, self)
        }
    }

    pub fn open_query(
        &self,
        context: Option<&Module>,
        predicate: &Predicate,
        args: &[&Term],
    ) -> Context<Query> {
        self.assert_activated();
        let context = context
            .map(|c| c.module_ptr())
            .unwrap_or(std::ptr::null_mut());
        let flags = PL_Q_NORMAL | PL_Q_PASS_EXCEPTION | PL_Q_EXT_STATUS;
        let terms = unsafe { PL_new_term_refs(args.len().try_into().unwrap()) };
        for i in 0..args.len() {
            let term = unsafe { self.wrap_term_ref(terms + i) };
            assert!(term.unify(args[i]).unwrap());
        }

        let qid = unsafe {
            PL_open_query(
                context,
                flags.try_into().unwrap(),
                predicate.predicate_ptr(),
                terms,
            )
        };

        let query = Query { qid, closed: false };

        self.activated.store(false, Ordering::Relaxed);
        Context {
            parent: Some(self),
            context: query,
            engine: self.engine,
            activated: AtomicBool::new(true),
        }
    }

    pub fn term_from_string(&self, s: &str) -> Option<Term> {
        let term = self.new_term_ref();
        let frame = self.open_frame();

        let arg1 = frame.new_term_ref();
        let arg3 = frame.new_term_ref();

        assert!(arg1.unify(s).unwrap());
        assert!(arg3.unify(Nil).unwrap());

        let query = read_term_from_atom(&frame, &arg1, &term, &arg3);

        let result = match query.next_solution() {
            QueryResult::SuccessLast => Some(term),
            _ => None,
        };
        query.cut();
        frame.close_frame();

        result
    }

    pub fn open_call(&self, t: &Term) -> Context<Query> {
        // TODO: must cache this
        let functor_call = self.new_functor("call", 1);
        let module = self.new_module("user");
        let predicate = self.new_predicate(&functor_call, &module);

        self.open_query(None, &predicate, &[&t])
    }
}

#[derive(Debug, Error)]
pub enum DetError {
    #[error("unexpected failure")]
    UnexpectedFailure,
    #[error("unexpected choice point")]
    UnexpectedChoicepoint,
    #[error("exception")]
    Exception,
}

pub type DetResult = Result<(), DetError>;

#[derive(Debug, Error)]
pub enum SemidetError {
    #[error("unexpected choice point")]
    UnexpectedChoicepoint,
    #[error("exception")]
    Exception,
}

impl From<SemidetError> for DetError {
    fn from(e: SemidetError) -> DetError {
        match e {
            SemidetError::UnexpectedChoicepoint => DetError::UnexpectedChoicepoint,
            SemidetError::Exception => DetError::Exception,
        }
    }
}

pub fn semidet_to_det_result(result: SemidetResult) -> DetResult {
    match result {
        Ok(true) => Ok(()),
        Ok(false) => Err(DetError::UnexpectedFailure),
        Err(e) => Err(e.into()),
    }
}

pub type SemidetResult = Result<bool, SemidetError>;

pub enum QueryResult<'a> {
    Success,
    SuccessLast,
    Failure,
    Exception(Term<'a>),
}

impl<'a> QueryResult<'a> {
    pub fn is_success(&self) -> bool {
        match self {
            Self::Success => true,
            Self::SuccessLast => true,
            _ => false,
        }
    }

    pub fn is_last(&self) -> bool {
        match self {
            Self::SuccessLast => true,
            Self::Failure => true,
            _ => false,
        }
    }

    pub fn is_nonlast_success(&self) -> bool {
        match self {
            Self::Success => true,
            _ => false,
        }
    }

    pub fn is_last_success(&self) -> bool {
        match self {
            Self::SuccessLast => true,
            _ => false,
        }
    }

    pub fn is_failure(&self) -> bool {
        match self {
            Self::Failure => true,
            _ => false,
        }
    }

    pub fn is_exception(&self) -> bool {
        match self {
            Self::Exception(_) => true,
            _ => false,
        }
    }

    pub fn exception(&self) -> Option<Term> {
        match self {
            Self::Exception(term) => Some(term.clone()),
            _ => None,
        }
    }
}

impl<'a> Context<'a, Query> {
    pub fn next_solution(&self) -> QueryResult {
        self.assert_activated();
        let result = unsafe { PL_next_solution(self.context.qid) };
        // TODO handle exceptions properly
        match result {
            -1 => {
                //let exception = unsafe { PL_exception(self.context.qid) };
                let exception = unsafe { PL_exception(0) };
                let exception_term = unsafe { self.wrap_term_ref(exception) };
                QueryResult::Exception(exception_term)
            }
            0 => QueryResult::Failure,
            1 => QueryResult::Success,
            2 => QueryResult::SuccessLast,
            _ => panic!("unknown query result type {}", result),
        }
    }

    pub fn cut(mut self) {
        self.assert_activated();
        // TODO handle exceptions
        unsafe { PL_cut_query(self.context.qid) };
        self.context.closed = true;
    }

    pub fn discard(mut self) {
        self.assert_activated();
        // TODO handle exceptions

        unsafe { PL_close_query(self.context.qid) };
        self.context.closed = true;
    }
}

impl Drop for Query {
    fn drop(&mut self) {
        // honestly, since closing a query may result in exceptions,
        // this is too late. We'll just assume the user intended to
        // discard, to encourage proper closing.
        if !self.closed {
            unsafe { PL_close_query(self.qid) };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::predicates;
    #[test]
    fn get_term_ref_on_fresh_engine() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let _term = context.new_term_ref();
    }

    #[test]
    fn get_term_ref_on_frame() {
        initialize_swipl_noengine();
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
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context1: Context<_> = activation.into();
        let _context2 = context1.open_frame();

        let _term = context1.new_term_ref();
    }

    #[test]
    fn query_det() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let functor_is = context.new_functor("is", 2);
        let functor_plus = context.new_functor("+", 2);
        let module = context.new_module("user");
        let predicate = context.new_predicate(&functor_is, &module);

        let term1 = context.new_term_ref();
        let term2 = context.new_term_ref();

        assert!(term2.unify(&functor_plus).unwrap());
        assert!(term2.unify_arg(1, 40_u64).unwrap());
        assert!(term2.unify_arg(2, 2_u64).unwrap());

        let query = context.open_query(None, &predicate, &[&term1, &term2]);
        let next = query.next_solution();

        assert!(next.is_success() && next.is_last());
        assert_eq!(42_u64, term1.get().unwrap());

        let next = query.next_solution();
        assert!(next.is_failure());
    }

    #[test]
    fn query_auto_discard() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let functor_is = context.new_functor("is", 2);
        let functor_plus = context.new_functor("+", 2);
        let module = context.new_module("user");
        let predicate = context.new_predicate(&functor_is, &module);

        let term1 = context.new_term_ref();
        let term2 = context.new_term_ref();

        assert!(term2.unify(&functor_plus).unwrap());
        assert!(term2.unify_arg(1, 40_u64).unwrap());
        assert!(term2.unify_arg(2, 2_u64).unwrap());

        {
            let query = context.open_query(None, &predicate, &[&term1, &term2]);
            let next = query.next_solution();

            assert!(next.is_last_success());
            assert_eq!(42_u64, term1.get().unwrap());
        }

        // after leaving the block, we have discarded
        assert!(term1.get::<u64>().is_none());
    }

    #[test]
    fn query_manual_discard() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let functor_is = context.new_functor("is", 2);
        let functor_plus = context.new_functor("+", 2);
        let module = context.new_module("user");
        let predicate = context.new_predicate(&functor_is, &module);

        let term1 = context.new_term_ref();
        let term2 = context.new_term_ref();

        assert!(term2.unify(&functor_plus).unwrap());
        assert!(term2.unify_arg(1, 40_u64).unwrap());
        assert!(term2.unify_arg(2, 2_u64).unwrap());

        {
            let query = context.open_query(None, &predicate, &[&term1, &term2]);
            let next = query.next_solution();

            assert!(next.is_last_success());
            assert_eq!(42_u64, term1.get().unwrap());
            query.discard();
        }

        // after leaving the block, we have discarded
        assert!(term1.get::<u64>().is_none());
    }

    #[test]
    fn query_cut() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let functor_is = context.new_functor("is", 2);
        let functor_plus = context.new_functor("+", 2);
        let module = context.new_module("user");
        let predicate = context.new_predicate(&functor_is, &module);

        let term1 = context.new_term_ref();
        let term2 = context.new_term_ref();

        assert!(term2.unify(&functor_plus).unwrap());
        assert!(term2.unify_arg(1, 40_u64).unwrap());
        assert!(term2.unify_arg(2, 2_u64).unwrap());

        {
            let query = context.open_query(None, &predicate, &[&term1, &term2]);
            let next = query.next_solution();

            assert!(next.is_last_success());
            assert_eq!(42_u64, term1.get().unwrap());
            query.cut();
        }

        // a cut query leaves data intact
        assert_eq!(42_u64, term1.get().unwrap());
    }

    #[test]
    fn term_from_string_works() {
        initialize_swipl_noengine();
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
    fn open_call_nondet() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.term_from_string("member(X, [a,b,c])").unwrap();
        let term_x = context.new_term_ref();
        assert!(term.unify_arg(1, &term_x).unwrap());

        let query = context.open_call(&term);
        assert!(query.next_solution().is_nonlast_success());
        term_x.get_atomable(|a| assert_eq!("a", a.unwrap().name()));

        assert!(query.next_solution().is_nonlast_success());
        term_x.get_atomable(|a| assert_eq!("b", a.unwrap().name()));

        assert!(query.next_solution().is_last_success());
        term_x.get_atomable(|a| assert_eq!("c", a.unwrap().name()));

        assert!(query.next_solution().is_failure());
    }

    #[test]
    fn open_query_with_0_arg_predicate() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let functor = context.new_functor("true", 0);
        let module = context.new_module("user");
        let predicate = context.new_predicate(&functor, &module);

        let query = context.open_query(None, &predicate, &[]);
        assert!(query.next_solution().is_last_success());
    }

    #[test]
    fn freeze_exception_is_delayed_until_next_query() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.term_from_string("freeze(X, throw(foo))").unwrap();
        let term_x = context.new_term_ref();
        term.unify_arg(1, &term_x).unwrap();
        let query = context.open_call(&term);
        assert!(query.next_solution().is_last_success());
        query.cut();

        assert!(term_x.unify(42_u64).unwrap());

        let term = context.new_term_ref();
        term.unify(true).unwrap();
        let query = context.open_call(&term);
        let next = query.next_solution();
        assert!(next.is_exception());
        let exception_term = next.exception().unwrap();

        let atomable: Atomable = exception_term.get().unwrap();
        assert_eq!("foo", atomable.name());

        assert!(term.get::<u64>().is_none());
    }

    predicates! {
        det fn unify_with_42(_context, term) {
            term.unify_det(42_u64)
        }
    }

    #[test]
    fn register_foreign_predicate() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();

        assert!(register_unify_with_42());

        let context: Context<_> = activation.into();
        let term = context.new_term_ref();

        let functor = context.new_functor("unify_with_42", 1);
        let module = context.new_module("user");
        let predicate = context.new_predicate(&functor, &module);

        let query = context.open_query(None, &predicate, &[&term]);
        assert!(query.next_solution().is_success());
        assert_eq!(42, term.get::<u64>().unwrap());
    }

    prolog! {
        #[name("is")]
        fn prolog_arithmetic(term, e);
    }

    #[test]
    fn call_prolog_from_generated_rust_query_opener() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.new_term_ref();
        let expr = context.term_from_string("2+2").unwrap();

        let q = prolog_arithmetic(&context, &term, &expr);
        assert!(q.next_solution().is_success());
        assert_eq!(4, term.get::<u64>().unwrap());
    }
}
