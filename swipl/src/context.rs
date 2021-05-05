//! Prolog contexts.
//!
//! As you interact with SWI-Prolog, the underlying prolog engine
//! moves into different states, where different things are
//! allowed. We keep track of this underlying state through Context
//! objects.
//!
//! Currently, there's four kind of states that we keep track of:
//! - ActivatedEngine - this is the state an engine will be in when we
//!   just created it. If you're directly working with engines, this
//!   will be your initial state.
//! - Unmanaged - this is the state an engine will be in when prolog
//!   is calling into the rust library, for example, when a foreign
//!   predicate implemented in rust is being called.
//! - Framed - In any context, you can create a prolog frame. A prolog
//!   frame allows you to rewind the state of all prolog terms to their
//!   state at the time of frame creation.
//! - OpenCall - While calling into prolog, this is the context you'll
//!   be in as you're walking through the solutions. This is a special
//!   context where a lot of the normal features are disabled.
//!
//! Contexts are either active or inactive. A context starts out as
//! active, but as soon as you do something that creates a new context
//! (create a frame, open a query), the context will become
//! inactive. Once the created context is dropped, the original
//! context will become active again.
//!
//! With the exception of the OpenCall context, all contexts let you
//! create new term refs, which are handles to data on the prolog
//! stack. These term refs can only be created while the context is
//! active. However, they can be manipulated as long as the context
//! that created them exists. As soon as the context is dropped
//! though, the Term will become invalid and trying to do anything
//! with it will result in a compile error.
//!
//! The OpenCall context is special in that no new terms are allowed
//! to be created, nor are you allowed to open another query. It is
//! however possible to create a new frame in this context, which
//! would once again put you in a state where these things are
//! possible. Of course, you'll have to drop this frame before you're
//! able to manipulate the OpenCall context again (such as retrieving
//! the next solution from the query).
//!
//! Various operations may cause the underlying engine to go into an
//! exceptional state. This is signaled by these operations returning
//! an `Err(PrologError::Exception)`. This means that a special
//! exception term has been set. Most context operations are
//! impossible while in this state, and attempting to perform them
//! will result in a panic. Your options are either to return back
//! into prolog (if you're implementing a foreign predicate), which
//! will then raise this exception in prolog, or to clear the
//! exception.
use super::callable::*;
use super::engine::*;
use super::fli::*;
use super::module::*;
use super::result::*;
use super::term::*;

use std::cell::Cell;

use swipl_macros::{prolog, term};

pub(crate) unsafe fn with_cleared_exception<R>(f: impl FnOnce() -> R) -> R {
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

/// A term wrapper for the special exception term.
///
/// The exception term lives in a special place on the prolog stack
/// where frame rewinds have no effect.
pub struct ExceptionTerm<'a>(Term<'a>);

impl<'a> ExceptionTerm<'a> {
    /// Clear the exception, so that the engine is no longer in an
    /// exceptional state.
    pub fn clear_exception(self) {
        self.assert_term_handling_possible();

        unsafe { PL_clear_exception() }
    }

    /// Call the given function with a copy of the exception term in a context where the exception has been cleared.
    ///
    /// This function is marked unsafe because it is not safe to use
    /// the original ExceptionTerm from within the given function, but
    /// we still have a handle to it through self. The caller will
    /// have to ensure that the function that is passed in will not
    /// use this exception term.
    unsafe fn with_cleared_exception<'b, C: ContextType, R>(
        &'b self,
        ctx: &'b Context<C>,
        f: impl FnOnce(&Term) -> R,
    ) -> R {
        ctx.assert_activated();
        let backup_term_ref = PL_new_term_ref();
        assert!(PL_unify(backup_term_ref, self.0.term_ptr()) != 0);
        let backup_term = Term::new(backup_term_ref, ctx.as_term_origin());
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

/// A context that the underlying prolog engine is in.
///
/// See the module documentation for an explanation of this type.
pub struct Context<'a, T: ContextType> {
    parent: Option<&'a dyn ContextParent>,
    pub context: T,
    engine: PL_engine_t,
    activated: Cell<bool>,
    exception_handling: Cell<bool>,
}

impl<'a, T: ContextType> Context<'a, T> {
    unsafe fn new_activated_without_parent(context: T, engine: PL_engine_t) -> Self {
        Context {
            parent: None,
            context,
            engine,
            activated: Cell::new(true),
            exception_handling: Cell::new(false),
        }
    }

    pub(crate) unsafe fn new_activated<'b, T2: ContextType>(
        parent: &'a Context<'b, T2>,
        context: T,
        engine: PL_engine_t,
    ) -> Self {
        Context {
            parent: Some(parent as &dyn ContextParent),
            context,
            engine,
            activated: Cell::new(true),
            exception_handling: Cell::new(false),
        }
    }

    pub(crate) unsafe fn deactivate(&self) {
        self.activated.set(false)
    }

    /// Panics if this context is not active.
    pub fn assert_activated(&self) {
        if !self.activated.get() {
            panic!("tried to use inactive context");
        }
    }

    /// Panics if the engine is in an exceptional state.
    pub fn assert_no_exception(&self) {
        if self.has_exception() {
            panic!("tried to use context which has raised an exception");
        }
    }

    /// Returns the underlying engine pointer.
    pub fn engine_ptr(&self) -> PL_engine_t {
        self.engine
    }

    /// Return the engine pointer as a `TermOrigin`, which is used in the construction of a `Term` in unsafe code.
    fn as_term_origin(&self) -> TermOrigin {
        unsafe { TermOrigin::new(self.engine_ptr()) }
    }

    /// Wrap the given term_t into a Term with a lifetime corresponding to this context.
    ///
    /// This is unsafe because there's no way of checking that the
    /// given term_t is indeed from this context. The caller will have
    /// to ensure that the term lives at least as long as this
    /// context.
    pub unsafe fn wrap_term_ref(&self, term: term_t) -> Term {
        self.assert_activated();
        Term::new(term, self.as_term_origin())
    }

    /// Put the engine in an exceptional state.
    ///
    /// The given term will be copied and put into the exception
    /// term. This function always returns
    /// `Err(PrologError::Exception)`.
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

    /// Returns true if the underlying engine is in an exceptional state.
    pub fn has_exception(&self) -> bool {
        self.assert_activated();

        unsafe { PL_exception(0) != 0 }
    }

    /// Clear the current exception if there is any.
    pub fn clear_exception(&self) {
        self.with_uncleared_exception(|e| match e {
            None => (),
            Some(e) => e.clear_exception(),
        })
    }

    /// Call the given function with the exception term, if it exists.
    ///
    /// The given function is able to clear the exception term, but
    /// not much else is allowed from safe code. Any attempt to do a
    /// get, put or unify with the given term will result in a panic.
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

    /// Call the given function with a copy of the exception term, from a context where the exception state has temporarily been cleared.
    ///
    /// This allows analysis on the exception term using all the
    /// normal safe functions for doing so. When the function returns,
    /// the engine will go back into an exceptional state with the
    /// original exception term.
    pub fn with_exception<'b, R>(&'b self, f: impl FnOnce(Option<&Term>) -> R) -> R {
        self.with_uncleared_exception(|e| match e {
            None => f(None),
            Some(e) => unsafe { e.with_cleared_exception(self, |e| f(Some(e))) },
        })
    }
}

trait ContextParent {
    fn reactivate(&self);
}

impl<'a, T: ContextType> ContextParent for Context<'a, T> {
    fn reactivate(&self) {
        if self.activated.replace(true) {
            panic!("context already active");
        }
    }
}

impl<'a, T: ContextType> Drop for Context<'a, T> {
    fn drop(&mut self) {
        if let Some(parent) = self.parent {
            parent.reactivate();
        }
    }
}

/// A type of context.
///
/// This is the object that is wrapped by [Context]. Implementors can
/// use this to hold context-specific information. Any functions are
/// to be implemented on `Context<YourContextType>`.
pub unsafe trait ContextType {}

/// Context type for an active engine. This wraps an `EngineActivation`.
///
/// Example:
/// ```
/// # use swipl::prelude::*;
/// let engine = Engine::new();
/// let activation = engine.activate();

/// let context: Context<ActivatedEngine> = activation.into();
/// // Note: Context<_> would also work as a type annotation
/// ```
pub struct ActivatedEngine<'a> {
    _activation: EngineActivation<'a>,
}

impl<'a> Into<Context<'a, ActivatedEngine<'a>>> for EngineActivation<'a> {
    fn into(self) -> Context<'a, ActivatedEngine<'a>> {
        let engine = self.engine_ptr();
        let context = ActivatedEngine { _activation: self };

        unsafe { Context::new_activated_without_parent(context, engine) }
    }
}

unsafe impl<'a> ContextType for ActivatedEngine<'a> {}

/// Context type for an unmanaged engine.
///
/// See [unmanaged_engine_context] for usage.
pub struct Unmanaged {
    // only here to prevent automatic construction
    _x: (),
}
unsafe impl ContextType for Unmanaged {}

/// Create an unmanaged context for situations where the thread has an engine that rust doesn't know about.
///
/// This is unsafe to call if we are not in a swipl environment, or if
/// some other context is active. Furthermore, the lifetime will most
/// definitely be wrong. This should be used by code that doesn't
/// promiscuously spread this context. all further accesses should be
/// through borrows.
///
/// Example:
/// ```
/// # use swipl::prelude::*;
/// # initialize_swipl_noengine();
/// # unsafe { swipl::fli::PL_thread_attach_engine(std::ptr::null_mut()); }
/// let context = unsafe { unmanaged_engine_context() };
/// # unsafe { swipl::fli::PL_thread_destroy_engine(); }
/// ```
pub unsafe fn unmanaged_engine_context() -> Context<'static, Unmanaged> {
    let current = current_engine_ptr();

    if current.is_null() {
        panic!("tried to create an unmanaged engine context, but no engine is active");
    }

    Context::new_activated_without_parent(Unmanaged { _x: () }, current)
}

enum FrameState {
    Active,
    Closed,
}

/// Context type for a prolog frame.
///
/// # Examples
/// Discard a frame through dropping:
/// ```
/// use swipl::prelude::*;
/// fn main() -> PrologResult<()> {
///    // create a context
///    let engine = Engine::new();
///    let activation = engine.activate();
///    let context: Context<_> = activation.into();
///
///    let term = context.new_term_ref();
///
///    {
///        let frame = context.open_frame();
///        term.unify(42_u64)?;
///    }
///
///    assert!(term.is_var());
///
///    Ok(())
/// }
/// ```
///
/// Discard a frame explicitely:
/// ```
/// use swipl::prelude::*;
/// fn main() -> PrologResult<()> {
///    // create a context
///    let engine = Engine::new();
///    let activation = engine.activate();
///    let context: Context<_> = activation.into();
///
///    let term = context.new_term_ref();
///
///    let frame = context.open_frame();
///    term.unify(42_u64)?;
///
///    frame.discard();
///    assert!(term.is_var());
///
///    Ok(())
/// }
/// ```
///
/// Close a frame:
/// ```
/// use swipl::prelude::*;
/// fn main() -> PrologResult<()> {
///    // create a context
///    let engine = Engine::new();
///    let activation = engine.activate();
///    let context: Context<_> = activation.into();
///
///    let term = context.new_term_ref();
///
///    let frame = context.open_frame();
///    term.unify(42_u64)?;
///    let term2 = frame.new_term_ref();
///
///    frame.close();
///    assert_eq!(42_u64, term.get()?);
///    // the following would result in a compile error:
///    // term2.unify(42_u64)?;
///
///    Ok(())
/// }
/// ```
///
/// Rewind a frame:
/// ```
/// use swipl::prelude::*;
/// fn main() -> PrologResult<()> {
///    // create a context
///    let engine = Engine::new();
///    let activation = engine.activate();
///    let context: Context<_> = activation.into();
///
///    let term = context.new_term_ref();
///
///    let frame = context.open_frame();
///    term.unify(42_u64)?;
///
///    let frame = frame.rewind();
///    // term is a variable again so the following unification will succeed
///    term.unify(43_u64)?;
///
///    frame.close();
///    assert_eq!(43_u64, term.get()?);
///
///    Ok(())
/// }
/// ```
///
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
    /// Close the frame.
    ///
    /// After closing, any terms created in the context of this frame
    /// will no longer be usable. Any data created and put in terms
    /// that are still in scope will be retained.
    pub fn close(mut self) {
        self.context.state = FrameState::Closed;
        // unsafe justification: reasons for safety are the same as in a normal drop. Also, since we just set framestate to discarded, the drop won't try to subsequently close this same frame.
        unsafe { PL_close_foreign_frame(self.context.fid) };
    }

    /// Discard the frame.
    ///
    /// This will destroy the frame. Any terms created in the context
    /// of this frame will no longer be usable. Furthermore, any term
    /// manipulation that happened since opening this frame will be
    /// undone. This is equivalent to a rewind followed by a close.
    pub fn discard(self) {
        // would happen automatically but might as well be explicit
        std::mem::drop(self)
    }

    /// Rewind the frame.
    ///
    /// This will rewind the frame. Any terms created in the context
    /// of this frame will no longer be usable. Furthermore, any term
    /// manipulation that happened since opening this frame will be
    /// undone.
    ///
    /// This returns a new context which is to be used for further
    /// manipulation of this frame.
    pub fn rewind(self) -> Context<'a, Frame> {
        self.assert_activated();
        // unsafe justification: We just checked that this frame right here is currently the active context. Therefore it can be rewinded.
        unsafe { PL_rewind_foreign_frame(self.context.fid) };

        self
    }
}

/// A trait marker for context types for which it is safe to open frames.
pub unsafe trait FrameableContextType: ContextType {}
unsafe impl FrameableContextType for Unmanaged {}
unsafe impl<'a> FrameableContextType for ActivatedEngine<'a> {}
unsafe impl FrameableContextType for Frame {}

impl<'a, C: FrameableContextType> Context<'a, C> {
    /// Open a new frame.
    ///
    /// This returns a new context for the frame. The current context
    /// will become inactive, until the new context is dropped. This
    /// may happen implicitely, when it goes out of scope, or
    /// explicitely, by calling `close()` or `discard()` on it.
    pub fn open_frame(&self) -> Context<Frame> {
        self.assert_activated();
        let fid = unsafe { PL_open_foreign_frame() };

        let frame = Frame {
            fid,
            state: FrameState::Active,
        };

        self.activated.set(false);
        unsafe { Context::new_activated(self, frame, self.engine) }
    }
}

/// A trait marker for context types for hich it is safe to open queries and create new term refs.
pub unsafe trait QueryableContextType: FrameableContextType {}
unsafe impl QueryableContextType for Unmanaged {}
unsafe impl<'a> QueryableContextType for ActivatedEngine<'a> {}
unsafe impl QueryableContextType for Frame {}

prolog! {
    #[module("user")]
    fn read_term_from_atom(atom_term, result, options);
    #[module("user")]
    #[name("call")]
    fn open_call(term);
}

impl<'a, T: QueryableContextType> Context<'a, T> {
    /// Create a new Term reference in the current context.
    ///
    /// The term ref takes on the lifetime of the Context reference,
    /// ensuring that it cannot outlive the context that created it.
    pub fn new_term_ref(&self) -> Term {
        self.assert_activated();
        unsafe {
            let term = PL_new_term_ref();
            Term::new(term, self.as_term_origin())
        }
    }

    /// Open a query.
    ///
    /// Example:
    /// ```
    /// # use swipl::prelude::*;
    /// # fn main() -> PrologResult<()> {
    /// #  let engine = Engine::new();
    /// #  let activation = engine.activate();
    /// #  let context: Context<_> = activation.into();
    ///
    ///    let query = context.open(pred!{format/2},
    ///                             [&term!{context: "hello, ~q~n"}?,
    ///                              &term!{context: ["world"]}?]);
    ///    query.next_solution()?;
    ///    query.cut();
    /// #
    /// #  Ok(())
    /// # }
    /// ```
    pub fn open<C: Callable<N>, const N: usize>(
        &self,
        callable: C,
        args: [&Term; N],
    ) -> Context<C::ContextType> {
        callable.open(self, None, args)
    }

    /// Open a query, get a single result and cut.
    ///
    /// Example:
    /// ```
    /// # use swipl::prelude::*;
    /// # fn main() -> PrologResult<()> {
    /// #  let engine = Engine::new();
    /// #  let activation = engine.activate();
    /// #  let context: Context<_> = activation.into();
    ///
    ///    context.call_once(pred!{format/2},
    ///                      [&term!{context: "hello, ~q~n"}?,
    ///                      &term!{context: ["world"]}?])?;
    /// #
    /// #  Ok(())
    /// # }
    /// ```
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

    /// Open a query, optionally passing in a context module.
    pub fn open_with_module<C: Callable<N>, const N: usize>(
        &self,
        callable: C,
        module: Option<Module>,
        args: [&Term; N],
    ) -> Context<C::ContextType> {
        callable.open(self, module, args)
    }

    /// Turn the given string into a prolog term.
    ///
    /// This uses the prolog predicate `read_term_from_atom/3` for the
    /// heavy lifting.
    ///
    /// Consider using the `term!` macro instead.
    pub fn term_from_string(&self, s: &str) -> PrologResult<Term> {
        let term = self.new_term_ref();
        let frame = self.open_frame();

        let arg1 = frame.new_term_ref();
        let arg3 = frame.new_term_ref();

        assert!(arg1.unify(s).is_ok());
        assert!(arg3.unify(Nil).is_ok());

        read_term_from_atom(&frame, &arg1, &term, &arg3).once()?;
        frame.close();

        Ok(term)
    }

    /// Open a query for the given term using the `call/1` prolog predicate.
    pub fn open_call(&'a self, t: &Term<'a>) -> Context<'a, impl OpenCall> {
        open_call(self, t)
    }

    /// Turn a result into a `PrologResult`.
    ///
    /// For this to work, the `Err` component of the `Result` needs to
    /// implement the trait `IntoPrologException`. This is currently
    /// only the case for [std::io::Error].
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

/// Trait for turning errors into prolog exceptions
pub trait IntoPrologException {
    /// Turns this error into a prolog exception using the given context.
    ///
    /// The result is a `Term` containing the prolog exception.
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

/// Call the given function, converting panics into prolog exceptions.
///
/// If the inner function panics, an exception of the form
/// `error(rust_error(panic("..the panic message..")))` will be
/// raised, and this function will return
/// `Err(PrologError::Exception)`. Otherwise, This function will
/// return `Ok(())`.
///
/// This is used by various macros to ensure that panics from user
/// code do not propagate into prolog.
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
    use crate::atom::*;
    use crate::functor::*;
    use crate::predicate::*;
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

        let functor_is = Functor::new("is", 2);
        let functor_plus = Functor::new("+", 2);
        let module = Module::new("user");
        let predicate = Predicate::new(functor_is, module);
        let callable = CallablePredicate::new(predicate).unwrap();

        let term1 = context.new_term_ref();
        let term2 = context.new_term_ref();

        term2.unify(functor_plus)?;
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

        let functor_is = Functor::new("is", 2);
        let functor_plus = Functor::new("+", 2);
        let module = Module::new("user");
        let predicate = Predicate::new(functor_is, module);
        let callable = CallablePredicate::new(predicate).unwrap();

        let term1 = context.new_term_ref();
        let term2 = context.new_term_ref();

        assert!(term2.unify(functor_plus).is_ok());
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

        let functor_is = Functor::new("is", 2);
        let functor_plus = Functor::new("+", 2);
        let module = Module::new("user");
        let predicate = Predicate::new(functor_is, module);
        let callable = CallablePredicate::new(predicate).unwrap();

        let term1 = context.new_term_ref();
        let term2 = context.new_term_ref();

        term2.unify(functor_plus)?;
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

        let functor_is = Functor::new("is", 2);
        let functor_plus = Functor::new("+", 2);
        let module = Module::new("user");
        let predicate = Predicate::new(functor_is, module);
        let callable = CallablePredicate::new(predicate).unwrap();

        let term1 = context.new_term_ref();
        let term2 = context.new_term_ref();

        term2.unify(functor_plus)?;
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
        let functor_foo = Functor::new("foo", 1);
        let functor_bar = Functor::new("bar", 2);

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

        let functor = Functor::new("true", 0);
        let module = Module::new("user");
        let predicate = Predicate::new(functor, module);
        let callable = CallablePredicate::new(predicate).unwrap();

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

        let functor = Functor::new("unify_with_42", 1);
        let module = Module::new("user");
        let predicate = Predicate::new(functor, module);
        let callable = CallablePredicate::new(predicate).unwrap();

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
