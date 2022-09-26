//! Support for easy text extraction from prolog.
use crate::fli;
use crate::term::*;
use crate::term_getable;

use std::os::raw::c_char;

/// A wrapper around an owned string for which [TermGetable](crate::term::TermGetable)
/// has been implemented.
///
/// This can be used to extract text both from atoms and from
/// strings. This is useful for contexts where we wish to accept
/// either one as an argument.
///
/// `PrologText` can be derefed to an `&String`, which means it's
/// automatically usable in most contexts that require one of those.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct PrologText(String);

impl PrologText {
    pub fn into_inner(self) -> String {
        self.0
    }
}

impl std::ops::Deref for PrologText {
    type Target = String;
    fn deref(&self) -> &String {
        &self.0
    }
}

term_getable! {
    (PrologText, "text", term) => {
        let mut len: usize = 0;
        let mut s: *mut c_char = std::ptr::null_mut();
        let flags = fli::CVT_ATOM|fli::CVT_STRING|fli::BUF_DISCARDABLE|fli::REP_UTF8;
        let result = unsafe { fli::PL_get_nchars(term.term_ptr(),
                                                 &mut len as *mut usize as *mut fli::size_t,
                                                 &mut s,
                                                 flags) };


        if result == 0 {
            None
        }
        else {
            let slice = unsafe { std::slice::from_raw_parts(s as *mut u8, len) };
            let string = std::str::from_utf8(slice).unwrap().to_string();

            Some(PrologText(string))
        }
    }
}
