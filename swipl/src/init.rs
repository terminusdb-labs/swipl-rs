//! Prolog initialization logic.
//!
//! When using swipl-rs to embed prolog, you need to ensure that you
//! initialize SWI-Prolog before you do anything else with
//! SWI-Prolog. The one exception is registering of foreign
//! predicates, which you're allowed to do at any point.
//!
//! Functions for both prolog initialization as well as foreign
//! predicate registration are defined here.

use crate::engine::*;
use crate::fli::*;

use lazy_static::*;
use std::convert::TryInto;
use std::ffi::CString;
use std::os::raw::{c_int, c_void};
use std::sync::{Arc, RwLock};

lazy_static! {
    static ref INITIALIZATION_STATE: Arc<RwLock<Option<Engine>>> = Arc::new(RwLock::new(None));
}

/// Activate the main prolog engine, or panic if it has alread been activated, or if SWI-Prolog was not initialized yet.
pub fn activate_main() -> EngineActivation<'static> {
    let initialized = INITIALIZATION_STATE.read().unwrap();
    unsafe { std::mem::transmute((*initialized).as_ref().unwrap().activate()) }
}

/// Check if SWI-Prolog has been initialized.
pub fn is_swipl_initialized() -> bool {
    unsafe { PL_is_initialised(std::ptr::null_mut(), std::ptr::null_mut()) != 0 }
}

/// Panic if SWI-Prolog has not been initialized.
pub fn assert_swipl_is_initialized() {
    if !is_swipl_initialized() {
        panic!("SWI-Prolog has not yet been initialized");
    }
}

static ARG0: &'static [u8] = b"rust-swipl\0"; // fake program name
static ARG1: &'static [u8] = b"--quiet\0"; // suppress swipl banner printing

/// Initialize SWI-Prolog.
///
/// This requires a borrow to a MainEngineActivator, whose lifetime will be used to
/// After initializing, the default 'main' engine is active on the
/// calling thread.  If SWI-Prolog was already initialized, this will
/// do nothing, and None will be returned. Otherwise, An
/// `EngineActivation` will be returned containing the main prolog
/// engine.
pub fn initialize_swipl() -> Option<EngineActivation<'static>> {
    if is_swipl_initialized() {
        return None;
    }

    // lock the rest of this initialization function to prevent concurrent initializers. Ideally this should happen in swipl itself, but unfortunately, it doesn't.
    let mut initialized = INITIALIZATION_STATE.write().unwrap();
    // There's actually a slight chance that initialization happened just now by some other thread. So check again.
    if initialized.is_some() {
        return None;
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
    *initialized = Some(unsafe { Engine::from_current() });

    Some(unsafe { std::mem::transmute((*initialized).as_ref().unwrap().set_activated()) })
}

/// Initialize SWI-Prolog and immediately deactivate the main thread engine.
///
/// If SWI-Prolog was already initialized, this will do nothing.
pub fn initialize_swipl_noengine() {
    let activation = initialize_swipl();
    // dropping the activation will deactivate the engine
    std::mem::drop(activation);
}

/// Reactivate the main engine.
///
/// This is only available if the rust library was originally
/// responsible for initializing the SWI-Prolog environment, and
/// the main engine has since been deactivated. If initialization
/// happened external to the library, there is no safe way to get
/// hold of the main engine. This will result in a panic.
pub fn reactivate_swipl() -> EngineActivation<'static> {
    let initialized = INITIALIZATION_STATE.read().unwrap();

    if let Some(engine) = initialized.as_ref() {
        unsafe { std::mem::transmute(engine.activate()) }
    } else {
        panic!("swipl-rs cannot reactiate the main engine because SWI-Prolog was not initialized, or initialized externally.");
    }
}

/// Register a foreign predicate.
///
/// This function is used by the `predicates!` macro to implement
/// predicate registration.
pub unsafe fn register_foreign_in_module(
    module: Option<&str>,
    name: &str,
    arity: u16,
    deterministic: bool,
    meta: Option<&str>,
    function_ptr: unsafe extern "C" fn(terms: term_t, arity: c_int, control: *mut c_void) -> isize,
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
    if is_swipl_initialized() && current_engine_ptr().is_null() {
        panic!("Tried to register a foreign predicate in a context where swipl is initialized, but no engine is active.");
    }

    let c_module = module.map(|module| CString::new(module).unwrap());
    let c_name = CString::new(name).unwrap();
    let c_meta = meta.map(|m| CString::new(m).unwrap());
    let mut flags = PL_FA_VARARGS;
    if !deterministic {
        flags |= PL_FA_NONDETERMINISTIC;
    }

    // an unfortunate need for transmute to make the fli eat the pointer
    let converted_function_ptr = std::mem::transmute(function_ptr);
    let c_module_ptr = c_module
        .as_ref()
        .map(|m| m.as_ptr())
        .unwrap_or(std::ptr::null_mut());

    PL_register_foreign_in_module(
        c_module_ptr,
        c_name.as_ptr(),
        arity as c_int,
        Some(converted_function_ptr),
        flags.try_into().unwrap(),
        c_meta
            .map(|m| m.as_ptr())
            .unwrap_or_else(|| std::ptr::null()),
    ) == 1
}
