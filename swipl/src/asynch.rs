use crate::callable::*;
use crate::context::*;
use crate::engine::*;
use crate::fli::*;
use crate::result::*;
use crate::term::*;

use async_trait::async_trait;
use futures::future::CatchUnwind;
use std::cell::Cell;
use std::future::Future;
use std::marker::PhantomData;
use std::panic::{catch_unwind, resume_unwind, UnwindSafe};
use std::pin::Pin;
use std::task::Poll;

trait AsyncContextParent {
    fn reactivate(&self);
}

impl<'a, T: AsyncContextType> AsyncContextParent for AsyncContext<'a, T> {
    fn reactivate(&self) {
        if self.activated.replace(true) {
            panic!("context already active");
        }
    }
}

pub unsafe trait AsyncContextType {}

pub struct AsyncActivatedEngine {
    _x: PhantomData<()>,
}

unsafe impl AsyncContextType for AsyncActivatedEngine {}

pub struct AsyncContext<'a, T: AsyncContextType> {
    parent: Option<&'a dyn AsyncContextParent>,
    pub context: T,
    engine: PL_engine_t,
    activated: Cell<bool>,
    exception_handling: Cell<bool>,
}

impl<'a, T: AsyncContextType> AsyncContext<'a, T> {
    unsafe fn new_activated_without_parent(context: T, engine: PL_engine_t) -> Self {
        AsyncContext {
            parent: None,
            context,
            engine,
            activated: Cell::new(true),
            exception_handling: Cell::new(false),
        }
    }

    pub(crate) unsafe fn new_activated<'b, T2: AsyncContextType>(
        parent: &'a AsyncContext<'b, T2>,
        context: T,
        engine: PL_engine_t,
    ) -> Self {
        AsyncContext {
            parent: Some(parent as &dyn AsyncContextParent),
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

    /// Returns true if the underlying engine is in an exceptional state.
    pub fn has_exception(&self) -> bool {
        self.assert_activated();

        unsafe { pl_default_exception() != 0 }
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

        let exception = unsafe { pl_default_exception() };
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
            Some(e) => unsafe { e.with_cleared_exception(self.as_term_origin(), |e| f(Some(e))) },
        })
    }

    /// Put the engine in an exceptional state.
    ///
    /// The given term will be copied and put into the exception
    /// term. This function always returns
    /// `Err(PrologError::Exception)`.
    pub fn raise_exception<R>(&self, term: &Term) -> PrologResult<R> {
        self.assert_activated();
        if term.is_var() {
            panic!("tried to raise a var as an exception");
        } else {
            unsafe {
                PL_raise_exception(term.term_ptr());
            }
        }

        Err(PrologError::Exception)
    }
}

impl<'a, T: AsyncContextType> Drop for AsyncContext<'a, T> {
    fn drop(&mut self) {
        if let Some(parent) = self.parent {
            parent.reactivate();
        }
    }
}

impl<'a> AsyncContext<'a, Frame> {
    /// Close the frame.
    ///
    /// After closing, any terms created in the context of this frame
    /// will no longer be usable. Any data created and put in terms
    /// that are still in scope will be retained.
    pub fn close(mut self) {
        // unsafe justification: reasons for safety are the same as in a normal drop. Also, since we just set framestate to discarded, the drop won't try to subsequently close this same frame.
        unsafe { self.context.close(); }
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
    pub fn rewind(mut self) -> AsyncContext<'a, Frame> {
        self.assert_activated();
        // unsafe justification: We just checked that this frame right here is currently the active context. Therefore it can be rewinded.
        unsafe { self.context.rewind(); }

        self
    }
}

/// A trait marker for context types for which it is safe to open frames.
pub unsafe trait FrameableAsyncContextType: AsyncContextType {}
unsafe impl FrameableAsyncContextType for AsyncActivatedEngine {}

unsafe impl AsyncContextType for Frame {}
unsafe impl FrameableAsyncContextType for Frame {}

impl<'a, C: FrameableAsyncContextType> AsyncContext<'a, C> {
    /// Open a new frame.
    ///
    /// This returns a new context for the frame. The current context
    /// will become inactive, until the new context is dropped. This
    /// may happen implicitely, when it goes out of scope, or
    /// explicitely, by calling `close()` or `discard()` on it.
    pub fn open_frame(&self) -> AsyncContext<Frame> {
        self.assert_activated();
        let frame = unsafe {Frame::open()};

        self.activated.set(false);
        unsafe { AsyncContext::new_activated(self, frame, self.engine) }
    }
}

/// A trait marker for context types for hich it is safe to open queries and create new term refs.
pub unsafe trait QueryableAsyncContextType: FrameableAsyncContextType {}
unsafe impl QueryableAsyncContextType for AsyncActivatedEngine {}
unsafe impl QueryableAsyncContextType for Frame {}

impl<'a, T: QueryableAsyncContextType> AsyncContext<'a, T> {
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
}

struct EngineActivationFuture<'a, T, F: Future<Output = T> + Send + UnwindSafe> {
    engine: &'a Engine,
    inner: Option<CatchUnwind<F>>,
}

impl<'a, T, F: Future<Output = T> + Send + UnwindSafe> Future for EngineActivationFuture<'a, T, F> {
    type Output = T;
    fn poll(
        self: Pin<&mut Self>,
        ctx: &mut std::task::Context<'_>,
    ) -> Poll<<Self as Future>::Output> {
        if self.inner.is_none() {
            panic!("future already dropped");
        }
        let engine = self.engine;
        engine.unchecked_activate();
        let inner = unsafe { self.map_unchecked_mut(|a| a.inner.as_mut().unwrap()) };
        let result = inner.poll(ctx);
        engine.unchecked_deactivate();

        match result {
            Poll::Pending => Poll::Pending,
            Poll::Ready(Ok(r)) => Poll::Ready(r),
            Poll::Ready(Err(e)) => {
                resume_unwind(e);
            }
        }
    }
}

impl<'a, T, F: Future<Output = T> + Send + UnwindSafe> Drop for EngineActivationFuture<'a, T, F> {
    fn drop(&mut self) {
        // When dropping, we have to take into account that the inner
        // future potentially needs the engine activated to do its
        // work, such as rewinding frames, closing queries, etc.
        //
        // We know swipl has been initialized, or we would have never
        // been able to make this future object in the first
        // place. Furthermore, we know that our inner engine is not
        // active elsewhere, as this future is in control of the
        // engine, and outside of drop, it only activates the engine
        // during poll. We can therefore safely temporarily set the
        // engine to our inner engine, do the drop of our inner
        // future, and then reset the engine to whatever it was before
        // this drop.
        //
        // Some care has to be taken to ensure that in case of a
        // panic, we still do the required engine setting.
        let mut inner = None;
        std::mem::swap(&mut inner, &mut self.inner);
        if let Some(inner) = inner {
            let mut current = std::ptr::null_mut();
            unsafe {
                PL_set_engine(self.engine.engine_ptr, &mut current);
            }
            let result = catch_unwind(|| std::mem::drop(inner));
            unsafe {
                PL_set_engine(current, std::ptr::null_mut());
            }

            if let Err(e) = result {
                resume_unwind(e);
            }

            unsafe {
                self.engine.set_deactivated();
            }
        }
    }
}
