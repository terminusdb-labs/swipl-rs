//! Prolog engines.
//!
//! A single process can run multiple prolog engines. Prolog engines
//! are somewhat equivalent to a prolog thread. However, it is
//! possible to move them between threads, or run multiple engines on
//! the same thread. From the perspective of prolog though, a single
//! engine corresponds with a single flow of execution.
//!
//! When using swipl-rs to implement foreign predicates as part of a
//! loadable module, you generally do not have to worry about prolog
//! engines, unless you're spawning extra threads.
use std::sync::atomic;

use crate::fli::*;
use crate::init::*;

/// A Prolog engine.
///
/// Prolog engines can be active or inactive. When activated, an
/// `EngineActivation` is returned, which when dropped will set the
/// engine back into an inactive state.
#[derive(Debug)]
pub struct Engine {
    engine_ptr: PL_engine_t,
    active: atomic::AtomicBool,
}

unsafe impl Send for Engine {}
unsafe impl Sync for Engine {}

/// A prolog engine activation.
///
/// When activating a prolog engine, this object is returned. The
/// object is guaranteed to not outlive the engine it was created
/// from. Furthermore, any one engine can have at most one activation
/// in existence at any time, and each thread can have at most one
/// engine activated on it.
#[derive(Debug)]
pub struct EngineActivation<'a> {
    engine: &'a Engine,
    _x: std::marker::PhantomData<*mut ()>,
}

impl<'a> EngineActivation<'a> {
    /// Returns the engine pointer of the engine associated with this activation.
    pub fn engine_ptr(&self) -> PL_engine_t {
        self.engine.engine_ptr
    }
}

//const PL_ENGINE_MAIN: PL_engine_t = 1 as PL_engine_t;
const PL_ENGINE_CURRENT: PL_engine_t = 2 as PL_engine_t;

/// Returns the current engine pointer.
///
/// This is unsafe because behavior of this function is undefined if
/// SWI-Prolog has not yet been activated.
pub unsafe fn current_engine_ptr() -> PL_engine_t {
    let mut current = std::ptr::null_mut();
    // This following bit is what makes this function unsafe.
    // This will behave in undefined ways if swipl has not been initialized.
    PL_set_engine(PL_ENGINE_CURRENT, &mut current);

    current
}

impl Engine {
    /// Create a new prolog engine.
    ///
    /// If SWI-Prolog has not been initialized yet, it'll be done here.
    pub fn new() -> Engine {
        initialize_swipl_noengine();
        // unsafe justification: creating a swipl engine is allowed from any thread as long as swipl has been initialized
        let engine_ptr = unsafe { PL_create_engine(std::ptr::null_mut()) };

        Engine {
            engine_ptr,
            active: atomic::AtomicBool::new(false),
        }
    }

    pub(crate) unsafe fn from_current() -> Engine {
        Engine {
            engine_ptr: current_engine_ptr(),
            active: atomic::AtomicBool::new(false),
        }
    }

    /// Returns true if some engine is currently active on this thread.
    pub fn some_engine_active() -> bool {
        if !is_swipl_initialized() {
            return false;
        }
        // unsafe justification: swipl was shown to be initialized above so engine should be queryable
        let current = unsafe { current_engine_ptr() };

        if current.is_null() {
            false
        } else {
            true
        }
    }

    /// Returns true if this engine is the engine currently active on this thread.
    pub fn is_active(&self) -> bool {
        is_engine_active(self.engine_ptr)
    }

    pub(crate) unsafe fn set_activated(&self) -> EngineActivation {
        if self
            .active
            .compare_exchange(
                false,
                true,
                atomic::Ordering::Relaxed,
                atomic::Ordering::Relaxed,
            )
            .is_err()
        {
            panic!("engine already activated");
        }

        EngineActivation {
            engine: self,
            _x: Default::default(),
        }
    }

    /// Activate this engine.
    ///
    /// This will panic if an engine is already active on this
    /// thread. Otherwise, it'll return an `EngineActivation` whose
    /// lifetime is bound to this engine.
    pub fn activate(&self) -> EngineActivation {
        if Self::some_engine_active() {
            panic!("tried to activate engine on a thread that already has an active engine");
        }

        if self
            .active
            .compare_exchange(
                false,
                true,
                atomic::Ordering::Relaxed,
                atomic::Ordering::Relaxed,
            )
            .is_err()
        {
            panic!("engine already activated");
        }

        // unsafe justification: swipl should have been initialized.
        let result = unsafe { PL_set_engine(self.engine_ptr, std::ptr::null_mut()) };

        match result as u32 {
            PL_ENGINE_SET => EngineActivation {
                engine: self,
                _x: Default::default(),
            },
            PL_ENGINE_INUSE => panic!("engine already activated"),
            PL_ENGINE_INVAL => panic!("engine handle not recognized by swipl"),
            _ => panic!("unknown result from PL_set_engine"),
        }
    }
}

/// Checks if the given engine pointer is the engine that is currently active on this thread.
///
/// This will panic is SWI-Prolog was not yet initialized.
pub fn is_engine_active(engine: PL_engine_t) -> bool {
    assert_swipl_is_initialized();
    let current = unsafe { current_engine_ptr() };

    current == engine
}

/// Panic if no engine is active on this thread.
pub fn assert_some_engine_is_active() {
    if !Engine::some_engine_active() {
        panic!("No SWI-Prolog engine is active");
    }
}

impl<'a> Drop for EngineActivation<'a> {
    fn drop(&mut self) {
        // unsafe justification: we have an engine context, so swipl was initialized. it should always be fine to set the current thread engine to nothing.
        self.engine.active.store(false, atomic::Ordering::Release);
        unsafe {
            PL_set_engine(std::ptr::null_mut(), std::ptr::null_mut());
        }
    }
}

impl Drop for Engine {
    fn drop(&mut self) {
        assert!(!self.active.load(atomic::Ordering::Relaxed));
        // unsafe justification: we got this ptr with PL_create_engine so this should be good
        unsafe {
            PL_destroy_engine(self.engine_ptr);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn create_and_activate_engine() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let _activation = engine.activate();
    }

    #[test]
    fn activate_deactivate_reactivate_engine() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        std::mem::drop(activation);
        let _activation = engine.activate();
    }

    #[test]
    fn switch_between_engines() {
        initialize_swipl_noengine();
        let engine1 = Engine::new();
        let engine2 = Engine::new();
        let activation1 = engine1.activate();
        std::mem::drop(activation1);
        let _activation2 = engine2.activate();
    }
}
