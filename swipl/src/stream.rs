//! Prolog streams.
//!
//! This exists mostly to support blob description writers. In the
//! future this will include more proper stream support.
use std::io::{self, Read, Write};
use std::marker::PhantomData;

use either::Either;
use num_enum::FromPrimitive;

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

    pub fn encoding(&self) -> StreamEncoding {
        StreamEncoding::from(unsafe { (*self.stream).encoding })
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
            fli::Sclearerr(stream);
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
        let error = fli::Sferror(stream);
        if error != 0 {
            fli::Sclearerr(stream);
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Tried to write data that is out of range for the encoding of this stream",
            ));
        }
        if result == fli::EOF {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "unexpected eof",
            ));
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
        let error = unsafe { fli::Sferror(self.stream) };
        if error != 0 {
            unsafe { fli::Sclearerr(self.stream) };
        }

        match (result, error) {
            (0, 0) => Ok(()),
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
        let error = unsafe { fli::Sferror(self.stream) };
        if error != 0 {
            unsafe { fli::Sclearerr(self.stream) };
        }
        match (result, error) {
            (0, 0) => Ok(()),
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

#[cfg(not(windows))]
#[derive(FromPrimitive)]
#[repr(u32)]
pub enum StreamEncoding {
    #[default]
    Unknown = 0,
    Octet,
    Ascii,
    Latin1,
    Ansi,
    Utf8,
    Utf16Be,
    Utf16Le,
    Wchar,
}

#[cfg(windows)]
#[derive(FromPrimitive)]
#[repr(i32)]
pub enum StreamEncoding {
    #[default]
    Unknown = 0,
    Octet,
    Ascii,
    Latin1,
    Ansi,
    Utf8,
    Utf16Be,
    Utf16Le,
    Wchar,
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

    pub fn encoding(&self) -> StreamEncoding {
        StreamEncoding::from(unsafe { (*self.stream).encoding })
    }

    /// Returns an implementation of Read which will automatically
    /// decode the underlying prolog stream, ensuring that it looks
    /// like proper utf-8.
    ///
    /// This is especially useful for cases where we like to pass a
    /// reader to a decoder like serde.
    pub fn decoding_reader(self) -> Either<Self, Latin1Reader<Self>> {
        match self.encoding() {
            StreamEncoding::Latin1 => Either::Right(Latin1Reader::new(self)),
            _ => Either::Left(self),
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
        fli::Sclearerr(stream);
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

pub struct Latin1Reader<R> {
    inner: R,
    remainder: u8,
}

impl<R> Latin1Reader<R> {
    pub fn new(reader: R) -> Self {
        Self {
            inner: reader,
            remainder: 0,
        }
    }

    pub fn into_inner(self) -> R {
        self.inner
    }
}

impl<R: Read> Read for Latin1Reader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if buf.is_empty() {
            return Ok(0);
        }
        let mut partial_buf = buf;
        let mut count = 0;
        if self.remainder != 0 {
            partial_buf[0] = self.remainder;
            partial_buf = &mut partial_buf[1..];
            count += 1;
            self.remainder = 0;
        }

        if partial_buf.is_empty() {
            return Ok(count);
        } else if partial_buf.len() == 1 {
            // only one character remains. we might be lucky and
            // be able to fit one more character, or we might hit
            // a boundary.
            let mut x = [0_u8; 1];
            let final_count = self.inner.read(&mut x)?;
            if final_count == 0 {
                return Ok(count);
            } else if x[0] & 0x80 != 0 {
                // boundary!
                let c = x[0] as char;
                let mut x2 = [0_u8; 2];
                c.encode_utf8(&mut x2);
                partial_buf[0] = x2[0];
                self.remainder = x2[1];
            } else {
                partial_buf[0] = x[0];
            }
            count += 1;
            return Ok(count);
        }
        // at least 2 bytes remain in buf. this means we can
        // always read at least one latin1 character.

        // for the most part we want to be optimistic and assume
        // that this latin-1 stream is actually just going to be
        // an ascii stream and no special encoding is necessary.
        // So we read directly into the destination buf and only
        // do something special if it turns out this assumption
        // doesn't hold.

        let expected_len = partial_buf.len() / 2;
        let mut len = self.inner.read(&mut partial_buf[..expected_len])?;
        if len == 0 {
            // nothing was read. we should be done.
            return Ok(count);
        }
        // scan for forbidden values
        let found_forbidden = partial_buf[..len].iter().position(|i| i & 0x80 != 0);
        if let Some(mut index) = found_forbidden {
            // copy remainder to a vec so we can start processing
            let copy = partial_buf[index..len].to_vec();
            for c in copy {
                (c as char).encode_utf8(&mut partial_buf[index..index + 2]);
                index += if c & 0x80 == 0 { 1 } else { 2 };
            }
            // finally, since length will have changed through this operation, ensure len is correct.
            len = index;
        }
        count += len;

        Ok(count)
    }
}
