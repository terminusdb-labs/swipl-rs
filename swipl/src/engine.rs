use lazy_static::*;
use std::convert::TryInto;
use std::ffi::CString;
use std::os::raw::{c_int, c_void};
use swipl_sys::*;

use std::sync::{atomic, Arc, RwLock};

lazy_static! {
    static ref INITIALIZATION_STATE: Arc<RwLock<bool>> = Arc::new(RwLock::new(false));
}

static ARG0: &'static [u8] = b"rust-swipl\0"; // fake program name
static ARG1: &'static [u8] = b"--quiet\0"; // suppress swipl banner printing

pub fn initialize_swipl() {
    {
        let initialized = INITIALIZATION_STATE.read().unwrap();
        if *initialized {
            return;
        }
    }

    // lock the rest of this initialization function to prevent concurrent initializers. Ideally this should happen in swipl itself, but unfortunately, it doesn't.
    let mut initialized = INITIALIZATION_STATE.write().unwrap();
    // There's actually a slight chance that initialization happened just now by some other thread. So check again.
    if *initialized {
        return;
    }

    // TOOD we just pick "rust-swipl" as a fake program name here. This seems to work fine. But what we should really do is pass along the actual argv[0].
    let mut args: [*mut i8; 3] = [
        ARG0.as_ptr() as *mut i8,
        ARG1.as_ptr() as *mut i8,
        std::ptr::null_mut(),
    ];
    // unsafe justification: this initializes the swipl library and is idempotent
    // That said, there is actually a chance that some non-rust code is concurrently initializing prolog, which may lead to errors. There is unfortunately nothing that can be done about this.
    unsafe { PL_initialise(2, args.as_mut_ptr()) };
    *initialized = true;
}

pub unsafe fn register_foreign_in_module(
    module: &str,
    name: &str,
    arity: u16,
    deterministic: bool,
    meta: Option<&str>,
    function_ptr: unsafe extern "C" fn(terms: term_t, arity: c_int, control: *mut c_void) -> usize,
) -> bool {
    if meta.is_some() && meta.unwrap().len() != arity as usize {
        panic!("supplied a meta argument that is not of equal length to the arity");
    }

    // We get a handle to the read guard of initialization state.
    // This ensures that we're either in the pre-initialization state
    // or the post-initialization state, but not currently
    // initializing.
    // if unitialized, no further checks are needed.
    // but if initialized, we need to ensure we're actually on an engine currently.
    let initialized = INITIALIZATION_STATE.read().unwrap();
    if *initialized && current_engine_ptr().is_null() {
        panic!("Tried to register a foreign predicate in a context where swipl is initialized, but no engine is active.");
    }

    let c_module = CString::new(module).unwrap();
    let c_name = CString::new(name).unwrap();
    let c_meta = meta.map(|m| CString::new(m).unwrap());
    let mut flags = PL_FA_VARARGS;
    if !deterministic {
        flags |= PL_FA_NONDETERMINISTIC;
    }

    // an unfortunate need for transmute to make the fli eat the pointer
    let converted_function_ptr = std::mem::transmute(function_ptr);

    PL_register_foreign_in_module(
        c_module.as_ptr(),
        c_name.as_ptr(),
        arity as c_int,
        Some(converted_function_ptr),
        flags.try_into().unwrap(),
        c_meta
            .map(|m| m.as_ptr())
            .unwrap_or_else(|| std::ptr::null()),
    ) == 1
}

pub fn initialize_swipl_noengine() {
    initialize_swipl();
    // unsafe justification: setting engine to nothing should always be allowed
    unsafe { PL_set_engine(std::ptr::null_mut(), std::ptr::null_mut()) };
}

#[derive(Debug)]
pub struct Engine {
    engine_ptr: PL_engine_t,
    active: atomic::AtomicBool,
}

#[derive(Debug)]
pub struct EngineActivation<'a> {
    engine: &'a Engine,
}

impl<'a> EngineActivation<'a> {
    pub fn engine_ptr(&self) -> PL_engine_t {
        self.engine.engine_ptr
    }
}

//const PL_ENGINE_MAIN: PL_engine_t = 1 as PL_engine_t;
const PL_ENGINE_CURRENT: PL_engine_t = 2 as PL_engine_t;

pub unsafe fn current_engine_ptr() -> PL_engine_t {
    let mut current = std::ptr::null_mut();
    // This following bit is what makes this function unsafe.
    // This will behave in undefined ways if swipl has not been initialized.
    PL_set_engine(PL_ENGINE_CURRENT, &mut current);

    current
}

impl Engine {
    pub fn new() -> Engine {
        initialize_swipl();
        // unsafe justification: creating a swipl engine is allowed from any thread as long as swipl has been initialized
        let engine_ptr = unsafe { PL_create_engine(std::ptr::null_mut()) };

        Engine {
            engine_ptr,
            active: atomic::AtomicBool::new(false),
        }
    }

    pub fn some_engine_active() -> bool {
        initialize_swipl();
        // unsafe justification: swipl was initialized above so engine should be queryable
        let current = unsafe { current_engine_ptr() };

        if current.is_null() {
            false
        } else {
            true
        }
    }

    pub fn is_active(&self) -> bool {
        is_engine_active(self.engine_ptr)
    }

    pub fn activate(&self) -> EngineActivation {
        if Self::some_engine_active() {
            panic!("tried to activate engine on a thread that already has an active engine");
        }

        if self
            .active
            .compare_and_swap(false, true, atomic::Ordering::Acquire)
        {
            panic!("engine already activated");
        }

        // unsafe justification: swipl should have been initialized.
        let result = unsafe { PL_set_engine(self.engine_ptr, std::ptr::null_mut()) };

        match result as u32 {
            PL_ENGINE_SET => EngineActivation { engine: self },
            PL_ENGINE_INUSE => panic!("engine already activated"),
            PL_ENGINE_INVAL => panic!("engine handle not recognized by swipl"),
            _ => panic!("unknown result from PL_set_engine"),
        }
    }
}

pub fn is_engine_active(engine: PL_engine_t) -> bool {
    // unsafe justification: swipl should have been initialized as we have an engine handle here
    let current = unsafe { current_engine_ptr() };

    current == engine
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
