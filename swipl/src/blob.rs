//! Blob support.
//!
//! Blobs are a way to share data with SWI-Prolog which does not fit
//! in any one of the built-in term types. They are stored in the
//! SWI-Prolog environment as a special kind of atom.
//!
//! This module, together with the various blob macros, implement
//! support for different classes of blobs.
//!
//! For all blob types, macros have been defined to easily define and
//! implement them. This allows your type to be used with
//! [Term::get](crate::term::Term::get),
//! [Term::put](crate::term::Term::put), and
//! [Term::unify](crate::term::Term::unify).
//!
//! # ArcBlob
//! This type of blob is a pointer to atomically reference counted
//! rust data. Upon getting, putting or unifying terms with data of
//! this type, only the pointer is transfered and reference counts are
//! updated.

//! ## Examples
//! Using the default implementation for `write` and `compare`:
//! ```
//! # use swipl::prelude::*;
//! # use std::sync::Arc;
//!
//! // note the keyword 'defaults' below - this makes sure that a
//! // default implementation of `ArcBlobImpl` is generated.
//! #[arc_blob("foo", defaults)]
//! struct Foo {
//!     num: u64
//! }
//!
//! fn do_something(term1: &Term, term2: &Term) -> PrologResult<()> {
//!     let arc = Arc::new(Foo{num: 42});
//!     term1.unify(&arc)?;
//!     let retrieved: Arc<Foo> = term1.get()?;
//!     assert_eq!(42, retrieved.num);
//!     term2.put(&retrieved)?;
//!
//!     Ok(())
//! }
//! ```
//!
//! Provide your own implementation for `write` and `compare`:
//! ```
//! # use swipl::prelude::*;
//! # use std::sync::Arc;
//! # use std::io::Write;
//! # use std::cmp::Ordering;
//!
//! #[arc_blob("foo")]
//! struct Foo {
//!     num: u64
//! }
//!
//! impl ArcBlobImpl for Foo {
//!     fn write(&self, stream: &mut PrologStream) -> std::io::Result<()> {
//!         write!(stream, "<foo {}>", self.num)
//!     }
//!
//!     fn compare(&self, other: &Self) -> Ordering {
//!         self.num.cmp(&other.num)
//!     }
//! }
//! ```
//!
//! # WrappedArcBlob
//! This type of blob is very similar to an [ArcBlob]. The difference
//! is that it is wrapped in a struct. This is done due to the
//! requirement that a trait from another crate can only be
//! implemented for your own types. This means that [ArcBlob] cannot
//! be directly implemented from code that depends on the `swipl`
//! crate for an `Arc` that comes out of another dependency. The
//! wrapper allows a trait to be implemented that does the job.
//!
//! ## Examples
//! Using the default implementation for `write` and `compare`:
//! ```
//! # use swipl::prelude::*;
//! # use std::sync::Arc;
//!
//! // Note that it is not possible to implement ArcBlob directly on a
//! // Vec<bool>, as it is not a type defined by us. That's why it
//! // needs to be wrapped.
//! wrapped_arc_blob!("foo", Foo, Vec<bool>, defaults);
//!
//! fn do_something(term1: &Term, term2: &Term) -> PrologResult<()> {
//!     let wrapped = Foo(Arc::new(vec![true,false,true]));
//!     term1.unify(&wrapped)?;
//!     let retrieved: Foo = term1.get()?;
//!     assert!(!retrieved[1]);
//!     term2.put(&retrieved)?;
//!
//!     Ok(())
//! }
//! ```
//!
//! Provide your own implementation for `write` and `compare`:
//! ```
//! # use swipl::prelude::*;
//! # use std::sync::Arc;
//! # use std::io::Write;
//! # use std::cmp::Ordering;
//!
//! wrapped_arc_blob!("foo", Foo, Vec<bool> );
//!
//! impl WrappedArcBlobImpl for Foo {
//!     fn write(this: &Vec<bool>, stream: &mut PrologStream) -> std::io::Result<()> {
//!         write!(stream, "<foo {:?}>",this)
//!     }
//!
//!     fn compare(this: &Vec<bool>, other: &Vec<bool>) -> Ordering {
//!         this.cmp(other)
//!     }
//! }
//! ```
//!
//! # CloneBlob
//! This type of blob copies its contents to and from SWI-Prolog when
//! getting, putting or unifying terms with the data.
//!
//! ## Examples
//! ```
//! # use swipl::prelude::*;
//!
//! // note the keyword 'defaults' below - this makes sure that a
//! // default implementation of `CloneBlobImpl` is generated.
//! // note also that the struct below derives Clone, which allows it
//! // to be used as a clone blob.
//! #[clone_blob("foo", defaults)]
//! #[derive(Clone)]
//! struct Foo {
//!     num: u64
//! }
//!
//! fn do_something(term1: &Term, term2: &Term) -> PrologResult<()> {
//!     let val = Foo{num: 42};
//!     term1.unify(&val)?;
//!     let retrieved: Foo = term1.get()?;
//!     assert_eq!(42, retrieved.num);
//!     term2.put(&retrieved)?;
//!
//!     Ok(())
//! }
//! ```
//!
//! Provide your own implementation for `write` and `compare`:
//! ```
//! # use swipl::prelude::*;
//! # use std::io::Write;
//! # use std::cmp::Ordering;
//!
//! #[clone_blob("foo")]
//! #[derive(Clone)]
//! struct Foo {
//!     num: u64
//! }
//!
//! impl CloneBlobImpl for Foo {
//!     fn write(&self, stream: &mut PrologStream) -> std::io::Result<()> {
//!         write!(stream, "<foo {}>", self.num)
//!     }
//!
//!     fn compare(&self, other: &Self) -> Ordering {
//!         self.num.cmp(&other.num)
//!     }
//! }
//! ```
//!
//! # wrapped CloneBlob
//! For convenience, there's also a
//! [wrapped_clone_blob!](crate::prelude::wrapped_clone_blob!) macro
//! for cases where we wish to generate a blob out of cloneable data
//! that is of a type defined in another crate. This is analogous to
//! the wrapped arc blob, except that no extra types are
//! required. There is no `WrappedCloneBlob`, instead, the wrapper
//! just implements CloneBlob directly.
//!
//! ## Examples
//! ```
//! # use swipl::prelude::*;
//!
//! wrapped_clone_blob!("foo", Foo, Vec<bool>, defaults);
//!
//! fn do_something(term1: &Term, term2: &Term) -> PrologResult<()> {
//!     let val = Foo(vec![true, false, true]);
//!     term1.unify(&val)?;
//!     let retrieved: Foo = term1.get()?;
//!     assert!(!retrieved[1]);
//!     term2.put(&retrieved)?;
//!
//!     Ok(())
//! }
//! ```
//!
//! Provide your own implementation for `write` and `compare`:
//! ```
//! # use swipl::prelude::*;
//! # use std::io::Write;
//! # use std::cmp::Ordering;
//!
//! wrapped_clone_blob!("foo", Foo, Vec<bool>);
//!
//! impl CloneBlobImpl for Foo {
//!     fn write(&self, stream: &mut PrologStream) -> std::io::Result<()> {
//!         write!(stream, "<foo {:?}>", self.0)
//!     }
//!
//!     fn compare(&self, other: &Self) -> Ordering {
//!         self.0.cmp(&other.0)
//!     }
//! }
//! ```

use std::cmp::Ordering;
use std::io::{self, Write};
use std::os::raw::{c_int, c_void};
use std::sync::Arc;

use crate::fli;
use crate::stream::*;
use crate::term::*;

/// Create a blob definition for use with the SWI-Prolog fli out of
/// the given components.
///
/// This is used by the various blob macros. You'll almost never have
/// to use this directly.
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

/// Base type for [ArcBlob].
///
/// This allows `blob_name` to be available to implementors of
/// [ArcBlobImpl], which is convenient for allowing auto-generation of
/// the write function.
pub trait ArcBlobBase {
    /// Return the name of this blob
    fn blob_name() -> &'static str;
}

/// Supertype of [ArcBlob] that allows implementation of `compare` and `write`.
///
/// When defining an [ArcBlob] through the
/// [arc_blob!](crate::prelude::arc_blob) attribute macro without the
/// 'defaults' argument, you're required to implement this trait for
/// your type. This allows you to modify how comparison and writing
/// will happen.
pub trait ArcBlobImpl: ArcBlobBase + Send + Sync + Unpin {
    /// Compare two values, returning an Ordering.
    ///
    /// This is used from SWI-Prolog when sorting lists. The default
    /// implementation returns `Ordering::Equal`, effectively
    /// providing no sorting information.
    fn compare(&self, _other: &Self) -> Ordering {
        Ordering::Equal
    }

    /// Write a description of this ArcBlob.
    ///
    /// The given stream implements [Write](std::io::Write), and
    /// therefore can be used with the [write!](std::write!) macro.
    ///
    /// The normal way of implementing this is to print something like
    /// `"<blob_name ..blob_data..>"`. The default implementation
    /// simply prints `"<blob_name>"`.
    fn write(&self, stream: &mut PrologStream) -> io::Result<()> {
        write!(stream, "<{}>", Self::blob_name())
    }
}

/// A blob type whose data is shared with SWI-Prolog as an atomic
/// reference-counted pointer.
///
/// This is unsafe because care has to be taken that the returned
/// `PL_blob_t` from `get_blob_definition` actually matches the blob
/// type.
pub unsafe trait ArcBlob: ArcBlobImpl {
    /// Return a blob definition for this ArcBlob.
    fn get_blob_definition() -> &'static fli::PL_blob_t;
}

/// Unify the term with the given `Arc`, using the given blob
/// definition to do so.
///
/// This is unsafe cause no attempt is made to ensure that the blob
/// definition matches the given data.
///
/// This is used from the arc blob macros.
pub unsafe fn unify_with_arc<T>(
    term: &Term,
    blob_definition: &'static fli::PL_blob_t,
    arc: &Arc<T>,
) -> bool {
    term.assert_term_handling_possible();

    let result = fli::PL_unify_blob(
        term.term_ptr(),
        Arc::as_ptr(arc) as *mut c_void,
        0,
        blob_definition as *const fli::PL_blob_t as *mut fli::PL_blob_t,
    );

    result != 0
}

/// Unify the term with the given Cloneable, using the given blob
/// definition to do so.
///
/// This is unsafe cause no attempt is made to ensure that the blob
/// definition matches the given data.
///
/// This is used from the clone blob macros.
pub unsafe fn unify_with_cloneable<T: Clone + Sized + Unpin>(
    term: &Term,
    blob_definition: &'static fli::PL_blob_t,
    val: &T,
) -> bool {
    term.assert_term_handling_possible();
    let cloned = val.clone();

    let result = fli::PL_unify_blob(
        term.term_ptr(),
        &cloned as *const T as *mut c_void,
        std::mem::size_of::<T>() as fli::size_t,
        blob_definition as *const fli::PL_blob_t as *mut fli::PL_blob_t,
    );

    if result != 0 {
        std::mem::forget(cloned);
        true
    } else {
        false
    }
}

/// Retrieve an arc from the given term, using the given blob
/// definition.
///
/// This is unsafe cause no attempt is made to ensure that the blob
/// definition matches the given data.
///
/// This is used from the arc blob macros.
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

/// Retrieve a cloneable value from the given term, using the given
/// blob definition.
///
/// This is unsafe cause no attempt is made to ensure that the blob
/// definition matches the given data.
///
/// This is used from the clone blob macros.
pub unsafe fn get_cloned_from_term<T: Clone + Sized + Unpin>(
    term: &Term,
    blob_definition: &'static fli::PL_blob_t,
) -> Option<T> {
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
        let cloned = (*data).clone();
        Some(cloned)
    }
}

/// Put an arc into the given term, using the given blob definition.
///
/// This is unsafe cause no attempt is made to ensure that the blob
/// definition matches the given data.
///
/// This is used from the arc blob macros.
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

/// Put a Cloneable into the given term, using the given blob
/// definition.
///
/// This is unsafe cause no attempt is made to ensure that the blob
/// definition matches the given data.
///
/// This is used from the clone blob macros.
pub unsafe fn put_cloneable_in_term<T: Clone + Sized + Unpin>(
    term: &Term,
    blob_definition: &'static fli::PL_blob_t,
    val: &T,
) {
    term.assert_term_handling_possible();

    let cloned = val.clone();

    fli::PL_put_blob(
        term.term_ptr(),
        &cloned as *const T as *mut c_void,
        std::mem::size_of::<T>() as fli::size_t,
        blob_definition as *const fli::PL_blob_t as *mut fli::PL_blob_t,
    );

    std::mem::forget(cloned);
}

/// Increment the reference count on an Arc stored in a blob.
///
/// This is used from the arc blob macros.
pub unsafe fn acquire_arc_blob<T>(atom: fli::atom_t) {
    let data = fli::PL_blob_data(atom, std::ptr::null_mut(), std::ptr::null_mut()) as *const T;

    Arc::increment_strong_count(data);
}

/// Decrement the reference count on an Arc stored in a blob.
///
/// This is used from the arc blob macros.
pub unsafe fn release_arc_blob<T>(atom: fli::atom_t) {
    let data = fli::PL_blob_data(atom, std::ptr::null_mut(), std::ptr::null_mut()) as *const T;

    Arc::decrement_strong_count(data);
}

/// Drop the rust value stored in a blob.
///
/// This is used from the clone blob macros.
pub unsafe fn release_clone_blob<T>(atom: fli::atom_t) {
    let data =
        fli::PL_blob_data(atom, std::ptr::null_mut(), std::ptr::null_mut()) as *const T as *mut T;

    std::ptr::drop_in_place(data);
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

    fn name() -> &'static str {
        T::blob_name()
    }
}

unsafe impl<T: ArcBlob> TermPutable for Arc<T> {
    fn put(&self, term: &Term) {
        let blob_definition = T::get_blob_definition();
        unsafe { put_arc_in_term(term, blob_definition, self) }
    }
}

/// Base type for [WrappedArcBlob].
///
/// This allows `blob_name` to be available to implementors of
/// [WrappedArcBlobImpl], which is convenient for allowing
/// auto-generation of the write function.
pub trait WrappedArcBlobBase {
    /// The type that the `WrappedArcBlob` is wrapping.
    type Inner: Send + Sync + Unpin;

    /// Return the name of this blob
    fn blob_name() -> &'static str;

    /// return a borrow to the wrapped Arc.
    fn get_arc(&self) -> &Arc<Self::Inner>;

    /// Create this wrapper from an Arc.
    fn from_arc(a: Arc<Self::Inner>) -> Self;
}

/// Supertype of [WrappedArcBlob] that allows implementation of
/// `compare` and `write`.
///
/// When defining a [WrappedArcBlob] through the
/// [wrapped_arc_blob!](crate::prelude::wrapped_arc_blob) macro
/// without the 'defaults' argument, you're required to implement this
/// trait for your type. This allows you to modify how comparison and
/// writing will happen.
pub trait WrappedArcBlobImpl: WrappedArcBlobBase {
    /// Compare two values, returning an Ordering.
    ///
    /// This is used from SWI-Prolog when sorting lists. The default
    /// implementation returns `Ordering::Equal`, effectively
    /// providing no sorting information.
    fn compare(_this: &Self::Inner, _other: &Self::Inner) -> Ordering {
        Ordering::Equal
    }

    /// Write a description of this WrappedArcBlob.
    ///
    /// The given stream implements [Write](std::io::Write), and
    /// therefore can be used with the [write!](std::write!) macro.
    ///
    /// The normal way of implementing this is to print something like
    /// `"<blob_name ..blob_data..>"`. The default implementation
    /// simply prints `"<blob_name>"`.
    fn write(_this: &Self::Inner, stream: &mut PrologStream) -> io::Result<()> {
        write!(stream, "<{}>", Self::blob_name())
    }
}

/// A blob type whose data is shared with SWI-Prolog as an atomic
/// reference-counted pointer, and which is wrapped into a wrapper
/// type.
///
/// This is unsafe because care has to be taken that the returned
/// `PL_blob_t` from `get_blob_definition` actually matches the blob
/// type.
pub unsafe trait WrappedArcBlob: WrappedArcBlobImpl {
    /// Return a blob definition for this WrappedArcBlob.
    fn get_blob_definition() -> &'static fli::PL_blob_t;
}

/// Base type for [CloneBlob].
///
/// This allows `blob_name` to be available to implementors of
/// [CloneBlobImpl], which is convenient for allowing auto-generation of
/// the write function.
pub trait CloneBlobBase {
    fn blob_name() -> &'static str;
}

/// Supertype of [CloneBlob] that allows implementation of `compare`
/// and `write`.
///
/// When defining a [CloneBlob] through the
/// [clone_blob!](crate::prelude::clone_blob) attribute macro without the
/// 'defaults' argument, you're required to implement this trait for
/// your type. This allows you to modify how comparison and writing
/// will happen.
pub trait CloneBlobImpl: CloneBlobBase + Sized + Sync + Clone {
    /// Compare two values, returning an Ordering.
    ///
    /// This is used from SWI-Prolog when sorting lists. The default
    /// implementation returns `Ordering::Equal`, effectively
    /// providing no sorting information.
    fn compare(&self, _other: &Self) -> Ordering {
        Ordering::Equal
    }

    /// Write a description of this ArcBlob.
    ///
    /// The given stream implements [Write](std::io::Write), and
    /// therefore can be used with the [write!](std::write!) macro.
    ///
    /// The normal way of implementing this is to print something like
    /// `"<blob_name ..blob_data..>"`. The default implementation
    /// simply prints `"<blob_name>"`.
    fn write(&self, stream: &mut PrologStream) -> io::Result<()> {
        write!(stream, "<{}>", Self::blob_name())
    }
}

/// A blob type whose data is copied into SWI-Prolog and dropped on
/// garbage collection.
///
/// This is unsafe because care has to be taken that the returned
/// `PL_blob_t` from `get_blob_definition` actually matches the blob
/// type.
pub unsafe trait CloneBlob: CloneBlobImpl {
    /// Return a blob definition for this CloneBlob.
    fn get_blob_definition() -> &'static fli::PL_blob_t;
}
