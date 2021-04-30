use std::cmp::Ordering;
use std::io::{self, Write};
use std::os::raw::{c_int, c_void};
use std::sync::Arc;

use crate::fli;
use crate::stream::*;
use crate::term::*;

pub fn create_blob_definition(
    name: &'static [u8],
    text: bool,
    unique: bool,
    nocopy: bool,
    acquire: Option<unsafe extern "C" fn(a: fli::atom_t)>,
    release: Option<unsafe extern "C" fn(a: fli::atom_t) -> c_int>,
    compare: Option<unsafe extern "C" fn(a: fli::atom_t, b: fli::atom_t) -> c_int>,
    write: Option<
        unsafe extern "C" fn(s: *mut fli::IOSTREAM, a: fli::atom_t, flags: c_int) -> c_int,
    >,
    save: Option<unsafe extern "C" fn(a: fli::atom_t, s: *mut fli::IOSTREAM) -> c_int>,
    load: Option<unsafe extern "C" fn(s: *mut fli::IOSTREAM) -> fli::atom_t>,
) -> fli::PL_blob_t {
    let last_char = name.last();
    if last_char.is_none() || *last_char.unwrap() != 0 {
        panic!("tried to register a blob definition with a name that does not end in a NULL");
    }

    let mut flags = 0;
    if text {
        flags |= fli::PL_BLOB_TEXT;
    }
    if unique {
        flags |= fli::PL_BLOB_UNIQUE;
    }
    if nocopy {
        flags |= fli::PL_BLOB_NOCOPY;
    }
    let mut result = unsafe { std::mem::zeroed::<fli::PL_blob_t>() };
    result.magic = fli::PL_BLOB_MAGIC as usize;
    result.flags = flags as usize;
    result.name = name.as_ptr() as *mut i8;
    result.acquire = acquire;
    result.release = release;
    result.compare = compare;
    result.write = write;
    result.save = save;
    result.load = load;

    result
}

pub trait ArcBlobInfo {
    fn blob_name() -> &'static str;
}

pub trait ArcBlobImpl: ArcBlobInfo + Send + Sync + Unpin {
    fn compare(&self, _other: &Self) -> Ordering {
        Ordering::Equal
    }
    fn write(&self, stream: &mut PrologStream) -> io::Result<()> {
        let blob_name = Self::blob_name();
        write!(stream, "<{}>", blob_name)
    }
}

pub unsafe trait ArcBlob: ArcBlobImpl {
    fn get_blob_definition() -> &'static fli::PL_blob_t;
}

pub unsafe fn unify_with_arc<T>(
    term: &Term,
    blob_definition: &'static fli::PL_blob_t,
    arc: &Arc<T>,
) -> bool {
    term.assert_term_handling_possible();

    let result = fli::PL_unify_blob(
        term.term_ptr(),
        Arc::as_ptr(arc) as *const T as *mut c_void,
        0,
        blob_definition as *const fli::PL_blob_t as *mut fli::PL_blob_t,
    );

    result != 0
}

pub unsafe fn get_arc_from_term<T>(
    term: &Term,
    blob_definition: &'static fli::PL_blob_t,
) -> Option<Arc<T>> {
    term.assert_term_handling_possible();

    let mut blob_type = std::ptr::null_mut();
    if fli::PL_is_blob(term.term_ptr(), &mut blob_type) == 0
        || blob_definition as *const fli::PL_blob_t != blob_type
    {
        return None;
    }

    let mut data: *mut T = std::ptr::null_mut();
    let result = fli::PL_get_blob(
        term.term_ptr(),
        &mut data as *mut *mut T as *mut *mut c_void,
        std::ptr::null_mut(),
        std::ptr::null_mut(),
    );

    if result == 0 {
        None
    } else {
        Arc::increment_strong_count(data);
        let arc = Arc::from_raw(data);
        Some(arc)
    }
}

pub unsafe fn put_arc_in_term<T>(
    term: &Term,
    blob_definition: &'static fli::PL_blob_t,
    arc: &Arc<T>,
) {
    term.assert_term_handling_possible();

    fli::PL_put_blob(
        term.term_ptr(),
        Arc::as_ptr(arc) as *mut c_void,
        0,
        blob_definition as *const fli::PL_blob_t as *mut fli::PL_blob_t,
    );
}

pub unsafe fn acquire_arc_blob<T>(atom: fli::atom_t) {
    let data = fli::PL_blob_data(atom, std::ptr::null_mut(), std::ptr::null_mut()) as *const T;

    Arc::increment_strong_count(data);
}

pub unsafe fn release_arc_blob<T>(atom: fli::atom_t) {
    let data = fli::PL_blob_data(atom, std::ptr::null_mut(), std::ptr::null_mut()) as *const T;

    Arc::decrement_strong_count(data);
}

unsafe impl<T: ArcBlob> Unifiable for Arc<T> {
    fn unify(&self, term: &Term) -> bool {
        let blob_definition = T::get_blob_definition();
        unsafe { unify_with_arc(term, blob_definition, self) }
    }
}

unsafe impl<T: ArcBlob> TermGetable for Arc<T> {
    fn get(term: &Term) -> Option<Self> {
        let blob_definition = T::get_blob_definition();
        unsafe { get_arc_from_term(term, blob_definition) }
    }
}

unsafe impl<T: ArcBlob> TermPutable for Arc<T> {
    fn put(&self, term: &Term) {
        let blob_definition = T::get_blob_definition();
        unsafe { put_arc_in_term(term, blob_definition, self) }
    }
}

pub trait WrappedArcBlobImpl {
    type Inner: Send + Sync + Unpin;
    fn get_arc(&self) -> &Arc<Self::Inner>;
    fn from_arc(a: Arc<Self::Inner>) -> Self;
    fn compare(this: &Self::Inner, other: &Self::Inner) -> Ordering;
    fn write(this: &Self::Inner, stream: &mut PrologStream);
}

pub unsafe trait WrappedArcBlob: WrappedArcBlobImpl {
    fn get_blob_definition() -> &'static fli::PL_blob_t;
}
