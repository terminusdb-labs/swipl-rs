//! Prolog streams.
//!
//! This exists mostly to support blob description writers. In the
//! future this will include more proper stream support.
use std::io::{self, Write};

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
        // We have to do the really stupid thing here of copying the
        // entire buffer just to add a zero byte at the end.  Would be
        // nice if there was a way to print to a prolog stream
        // specifying a length, but alas there is not.  There is
        // Sfwrite, but it just dumbly copies bytes without checking
        // encoding, so if encoding is multi-byte (as is the case in
        // DWIM), it messes up.
        let mut write_buf = Vec::with_capacity(buf.len() + 1);
        write_buf.extend_from_slice(buf);
        write_buf.push(0);
        unsafe { fli::Sfputs(write_buf.as_ptr() as *const i8, self.stream) };

        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        let result = unsafe { fli::Sflush(self.stream) };
        match result {
            0 => Ok(()),
            _ => Err(io::Error::new(io::ErrorKind::Other, "prolog flush failed")),
        }
    }
}
