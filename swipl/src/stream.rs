//! Prolog streams.
//!
//! This exists mostly to support blob description writers. In the
//! future this will include more proper stream support.
use std::io::{self, Write};
use std::os::raw::c_void;

use crate::fli;

/// A stream from prolog.
pub struct PrologStream {
    stream: *mut fli::IOSTREAM,
}

impl PrologStream {
    /// Wrap the underlying fli object.
    pub unsafe fn wrap(stream: *mut fli::IOSTREAM) -> Self {
        Self { stream }
    }
}

impl Write for PrologStream {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let count = unsafe {
            fli::Sfwrite(
                buf.as_ptr() as *const c_void,
                1,
                buf.len() as fli::size_t,
                self.stream,
            )
        };
        Ok(count as usize)
    }

    fn flush(&mut self) -> io::Result<()> {
        let result = unsafe { fli::Sflush(self.stream) };
        match result {
            0 => Ok(()),
            _ => Err(io::Error::new(io::ErrorKind::Other, "prolog flush failed")),
        }
    }
}
