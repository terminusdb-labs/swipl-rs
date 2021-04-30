use crate::fli;
use crate::term::*;
use crate::term_getable;

use std::os::raw::c_char;

pub struct PrologText(String);

impl std::ops::Deref for PrologText {
    type Target = String;
    fn deref(&self) -> &String {
        &self.0
    }
}

term_getable! {
    (PrologText, term) => {
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
