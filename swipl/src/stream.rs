//! Prolog streams.
//!
//! This exists mostly to support blob description writers. In the
//! future this will include more proper stream support.
use std::io::{self, Read, Write};
use std::marker::PhantomData;

use crate::engine::*;
use crate::term::*;
use crate::{fli, term_getable};

/// A stream from prolog, used in blob writers.
pub struct PrologStream {
    stream: *mut fli::IOSTREAM,
}

impl PrologStream {
    /// Wrap the underlying fli object.
    ///
    /// # Safety
    /// This is only safe to do with actual IOSTREAMs coming out of
    /// SWI-Prolog.
    pub unsafe fn wrap(stream: *mut fli::IOSTREAM) -> Self {
        Self { stream }
    }
}

/// A stream from prolog that can be directly written to.
///
/// This stream will be in a claimed state, meaning, any attempted
/// handling of this stream from another (prolog) thread will fail. On
/// drop, this claim will be released. It is therefore important to
/// drop this stream as soon as possible.
pub struct WritablePrologStream<'a> {
    stream: *mut fli::IOSTREAM,
    _x: PhantomData<&'a ()>,
}

impl<'a> WritablePrologStream<'a> {
    /// Wrap a writable prolog stream.
    ///
    /// # Safety
    /// This is only safe to do with actual IOSTREAMs coming out of
    /// SWI-Prolog, which are writable.
    pub unsafe fn new(stream: *mut fli::IOSTREAM) -> WritablePrologStream<'a> {
        WritablePrologStream {
            stream,
            _x: PhantomData,
        }
    }
}

impl<'a> Drop for WritablePrologStream<'a> {
    fn drop(&mut self) {
        unsafe {
            fli::PL_release_stream(self.stream);
        }
    }
}

term_getable! {
    // note that 'a is a known lifetime in this context, set up by the
    // macro, and it refers to the lifetime of the term's origin. This
    // means that the stream retrieved here cannot outlive that
    // origin.
    (WritablePrologStream<'a>, term) => {
        let mut stream: *mut fli::IOSTREAM = std::ptr::null_mut();
        if unsafe { fli::PL_get_stream(term.term_ptr(), &mut stream, fli::SH_OUTPUT|fli::SH_UNLOCKED|fli::SH_NOPAIR) } != 0 {
            Some(unsafe {WritablePrologStream::new(stream) })
        }
        else {
            None
        }
    }
}

unsafe fn ensure_writable_prolog_stream(stream: *mut fli::IOSTREAM) -> io::Result<()> {
    if (*stream).flags & fli::SIO_OUTPUT == 0 {
        Err(io::Error::new(
            io::ErrorKind::BrokenPipe,
            "prolog stream is not writable",
        ))
    } else {
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
            buf.len(),
            stream,
        );

        let error = fli::Sferror(stream);
        if error == -1 {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "unexpected eof",
            ));
        }
    } else {
        //eprintln!("indirect write! ({:?}", buf);
        let mut write_buf = Vec::with_capacity(buf.len() + 1);
        write_buf.extend_from_slice(buf);
        write_buf.push(0);
        let result = fli::Sfputs(write_buf.as_ptr() as *const std::os::raw::c_char, stream);
        if result == fli::EOF {
            if fli::Sferror(stream) != 0 {
                fli::Sclearerr(stream);
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "Tried to write data that is out of range for the encoding of this stream",
                ));
            } else {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "unexpected eof",
                ));
            }
        }

        count = buf.len();
    }

    Ok(count)
}

impl<'a> Write for WritablePrologStream<'a> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        assert_some_engine_is_active();

        unsafe { write_to_prolog_stream(self.stream, buf) }
    }

    fn flush(&mut self) -> io::Result<()> {
        assert_some_engine_is_active();
        let result = unsafe { fli::Sflush(self.stream) };
        match result {
            0 => Ok(()),
            _ => Err(io::Error::new(io::ErrorKind::Other, "prolog flush failed")),
        }
    }
}

impl Write for PrologStream {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        assert_some_engine_is_active();
        unsafe { write_to_prolog_stream(self.stream, buf) }
    }

    fn flush(&mut self) -> io::Result<()> {
        assert_some_engine_is_active();
        let result = unsafe { fli::Sflush(self.stream) };
        match result {
            0 => Ok(()),
            _ => Err(io::Error::new(io::ErrorKind::Other, "prolog flush failed")),
        }
    }
}

/// A stream from prolog that can be read from.
///
/// This stream will be in a claimed state, meaning, any attempted
/// handling of this stream from another (prolog) thread will fail. On
/// drop, this claim will be released. It is therefore important to
/// drop this stream as soon as possible.
pub struct ReadablePrologStream<'a> {
    stream: *mut fli::IOSTREAM,
    _x: PhantomData<&'a ()>,
}

impl<'a> ReadablePrologStream<'a> {
    /// Wrap a readable prolog stream.
    ///
    /// # Safety
    /// This is only safe to do with actual IOSTREAMs coming out of
    /// SWI-Prolog, which are readable.
    pub unsafe fn new(stream: *mut fli::IOSTREAM) -> ReadablePrologStream<'a> {
        ReadablePrologStream {
            stream,
            _x: PhantomData,
        }
    }
}

impl<'a> Drop for ReadablePrologStream<'a> {
    fn drop(&mut self) {
        unsafe {
            fli::PL_release_stream(self.stream);
        }
    }
}

term_getable! {
    // note that 'a is a known lifetime in this context, set up by the
    // macro, and it refers to the lifetime of the term's origin. This
    // means that the stream retrieved here cannot outlive that
    // origin.
    (ReadablePrologStream<'a>, term) => {
        let mut stream: *mut fli::IOSTREAM = std::ptr::null_mut();
        if unsafe { fli::PL_get_stream(term.term_ptr(), &mut stream, fli::SH_INPUT|fli::SH_UNLOCKED|fli::SH_NOPAIR) } != 0 {
            Some(unsafe {ReadablePrologStream::new(stream) })
        }
        else {
            None
        }
    }
}

unsafe fn ensure_readable_prolog_stream(stream: *mut fli::IOSTREAM) -> io::Result<()> {
    if (*stream).flags & fli::SIO_INPUT == 0 {
        Err(io::Error::new(
            io::ErrorKind::BrokenPipe,
            "prolog stream is not readable",
        ))
    } else {
        Ok(())
    }
}

unsafe fn read_from_prolog_stream(stream: *mut fli::IOSTREAM, buf: &mut [u8]) -> io::Result<usize> {
    ensure_readable_prolog_stream(stream)?;

    let count = fli::Sfread(
        buf.as_mut_ptr() as *mut std::ffi::c_void,
        1,
        buf.len(),
        stream,
    );

    let error = fli::Sferror(stream);
    if error == -1 {
        Err(io::Error::new(
            io::ErrorKind::UnexpectedEof,
            "unexpected eof",
        ))
    } else {
        Ok(count)
    }
}

impl<'a> Read for ReadablePrologStream<'a> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        assert_some_engine_is_active();

        unsafe { read_from_prolog_stream(self.stream, buf) }
    }
}
