//! Re-export of the swipl-fli crate.
pub use swipl_fli::*;

/// Retrieve the default exception.
pub unsafe fn pl_default_exception() -> term_t {
    // So why this ugly transmute?
    // In swipl version 8.5.5, query handles change from being a
    // simple number to a more complex pointer handle. PL_exception
    // can be called in two ways - either give it a pointer handle, or
    // give it a 0 to say you want the 'default' exception. In c, that
    // 0 automatically converts to either a null-pointer or the
    // numeric type it was before 8.5.5, but rust type checking is far
    // more strict.
    // By doing a transmute, we know we always get the right thing
    // from a 0.

    PL_exception(std::mem::transmute(0_u64))
}
