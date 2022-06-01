//! Prolog streams.
//!
//! This exists mostly to support blob description writers. In the
//! future this will include more proper stream support.
use std::io::{self, Write};

use crate::term::*;
use crate::{fli, term_getable};

/// A stream from prolog, used in blob writers.
pub struct PrologStream {
    stream: *mut fli::IOSTREAM,
}

impl PrologStream {
    /// Wrap the underlying fli object.
    pub unsafe fn wrap(stream: *mut fli::IOSTREAM) -> Self {
        Self { stream }
    }
}

/// A stream from prolog that can be directly written to.
pub struct WritablePrologStream {
    stream: *mut fli::IOSTREAM,
}

term_getable! {
    (WritablePrologStream, term) => {
        let mut stream: *mut fli::IOSTREAM = std::ptr::null_mut();
        if unsafe { fli::PL_get_stream(term.term_ptr(), &mut stream, fli::SH_OUTPUT|fli::SH_UNLOCKED|fli::SH_NOPAIR) } != 0 {
            Some(WritablePrologStream{stream})
        }
        else {
            None
        }
    }
}

unsafe fn ensure_writable_prolog_stream(stream: *mut fli::IOSTREAM) -> io::Result<()> {
    if (*stream).flags & fli::SIO_OUTPUT == 0 {
        Err(io::Error::new(io::ErrorKind::BrokenPipe, "prolog stream is not writable"))
    }
    else {
        Ok(())
    }
}

unsafe fn write_to_prolog_stream(stream: *mut fli::IOSTREAM, buf: &[u8]) -> io::Result<usize> {
    ensure_writable_prolog_stream(stream)?;
    let enc = (*stream).encoding;
    let count;
    if enc == fli::IOENC_ENC_OCTET || enc == fli::IOENC_ENC_ANSI || enc == fli::IOENC_ENC_UTF8 {
        // in this case we can just write our buf directly.
        //eprintln!("direct write! ({:?})", buf);
        count = fli::Sfwrite(
            buf.as_ptr() as *const std::ffi::c_void,
            1,
            buf.len() as fli::size_t,
            stream,
        ) as usize;
    } else {
        //eprintln!("indirect write! ({:?}", buf);
        let mut write_buf = Vec::with_capacity(buf.len() + 1);
        write_buf.extend_from_slice(buf);
        write_buf.push(0);
        let result = fli::Sfputs(write_buf.as_ptr() as *const i8, stream);
        if result == fli::EOF {
            if fli::Sferror(stream) != 0 {
                fli::Sclearerr(stream);
                return Err(io::Error::new(io::ErrorKind::InvalidData, "Tried to write data that is out of range for the encoding of this stream"));
            }
            else {
                return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "unexpected eof"));
            }
        }

        count = buf.len();
    }

    Ok(count)
}

impl Write for WritablePrologStream {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        unsafe { fli::PL_acquire_stream(self.stream) };

        let result = unsafe { write_to_prolog_stream(self.stream, buf) };

        unsafe { fli::PL_release_stream(self.stream) };

        result
    }

    fn flush(&mut self) -> io::Result<()> {
        unsafe { fli::PL_acquire_stream(self.stream) };
        let result = unsafe { fli::Sflush(self.stream) };
        unsafe { fli::PL_release_stream(self.stream) };
        match result {
            0 => Ok(()),
            _ => Err(io::Error::new(io::ErrorKind::Other, "prolog flush failed")),
        }
    }
}

impl Write for PrologStream {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        unsafe { write_to_prolog_stream(self.stream, buf) }
    }

    fn flush(&mut self) -> io::Result<()> {
        let result = unsafe { fli::Sflush(self.stream) };
        match result {
            0 => Ok(()),
            _ => Err(io::Error::new(io::ErrorKind::Other, "prolog flush failed")),
        }
    }
}
