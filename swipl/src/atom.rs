//! Prolog atoms.
//!
//! Atoms are a core datatype in prolog. An atom is a string that is
//! kept around in a lookup table. Each occurence of an atom for the
//! same string points at the same object. This allows for easy
//! comparison.
//!
//! Atoms are reference-counted. When nothing refers to an atom
//! anymore, the atom may be garbage collected, freeing up the memory
//! of the string.
//!
//! This module provides functions and types for interacting with
//! prolog atoms.

use super::engine::*;
use super::fli::*;
use super::init::*;
use super::result::*;
use super::term::*;
use crate::{term_getable, term_putable, unifiable};
use std::convert::TryInto;
use std::os::raw::c_char;

/// A wrapper for a prolog atom.
///
/// When created, the underlying atom will have its reference count
/// increased. When dropped, the reference count will decrease.
#[derive(PartialEq, Eq, Debug)]
pub struct Atom {
    atom: atom_t,
}

impl Atom {
    /// Wrap an `atom_t`, which is how the SWI-Prolog fli represents atoms.
    ///
    /// This is unsafe because no check is done to ensure that the
    /// atom_t indeed points at a valid atom. The caller will have to
    /// ensure that this is the case.
    pub unsafe fn wrap(atom: atom_t) -> Atom {
        Atom { atom }
    }

    /// Create a new atom from the given string.
    ///
    /// This will panic if no prolog engine is active on this thread.
    ///
    /// If the atom already exists, this will raise the reference
    /// count on that atom and then return the existing atom.
    pub fn new(name: &str) -> Atom {
        assert_swipl_is_initialized();
        // there's a worrying bit of information in the documentation.
        // It says that in some cases for small strings,
        // PL_new_atom_mbchars will recalculate the size of the string
        // using strlen. In that case we need to give it a
        // nul-terminated string.
        const S_USIZE: usize = std::mem::size_of::<usize>();
        let atom = if name.len() == S_USIZE - 1 {
            let mut buf: [u8; S_USIZE] = [0; S_USIZE];
            buf[..name.len()].clone_from_slice(name.as_bytes());

            unsafe {
                PL_new_atom_mbchars(
                    REP_UTF8.try_into().unwrap(),
                    name.len().try_into().unwrap(),
                    buf.as_ptr() as *const c_char,
                )
            }
        } else {
            unsafe {
                PL_new_atom_mbchars(
                    REP_UTF8.try_into().unwrap(),
                    name.len().try_into().unwrap(),
                    name.as_ptr() as *const c_char,
                )
            }
        };

        unsafe { Atom::wrap(atom) }
    }

    /// Return the underlying `atom_t` which SWI-Prolog uses to refer to the atom.
    pub fn atom_ptr(&self) -> atom_t {
        self.atom
    }

    /// Retrieve the name of this atom, that is, the string with which it was created.
    ///
    /// This will panic if no prolog engine is active on this thread.
    pub fn name(&self) -> &str {
        assert_some_engine_is_active();
        // TODO we're just assuming that what we get out of prolog is
        // utf-8. but it's not. On windows, a different encoding is
        // used and it is unclear to me if they convert to utf8 just
        // for this call. But they probably don't. Need to check.

        // TODO also the garbage collection is pretty
        // unclear. Documentation says that PL_atom_chars returns a
        // string not changed by prolog, valid until the atom is
        // garbage collected. assuming the nchars version is the same,
        // and assuming that documentation is right, it should be fine
        // to refer to this string for the entire lifetime of this
        // atom ref. However, whether this is actually the case
        // remains to be seen. Since different operating systems have
        // a different internal structure for atoms, it would follow
        // that on some platforms, this may in fact not be a pointer
        // into the atom string directly, but a copy onto the ring
        // buffer.

        // As a potential portable solution, we may have to unify with
        // a term first, and then extract the string from the term
        // directly. There are far better string extraction functions
        // for that case, which allow explicit specification of the
        // string format as utf-8.

        let mut size = 0;
        let ptr = unsafe { PL_atom_nchars(self.atom, &mut size) };

        let swipl_string_ref =
            unsafe { std::slice::from_raw_parts(ptr as *const u8, size as usize) };

        let swipl_string = std::str::from_utf8(swipl_string_ref).unwrap();

        swipl_string
    }
}

impl Clone for Atom {
    fn clone(&self) -> Self {
        assert_some_engine_is_active();
        unsafe { PL_register_atom(self.atom) };
        Atom { atom: self.atom }
    }
}

impl Drop for Atom {
    fn drop(&mut self) {
        assert_some_engine_is_active();
        unsafe {
            PL_unregister_atom(self.atom);
        }
    }
}

unifiable! {
    (self:Atom, term) => {
        let result = unsafe { PL_unify_atom(term.term_ptr(), self.atom) };

        result != 0
    }
}

/// Get an atom out of a term.
///
/// This is unsafe because we don't check if the term is part of the
/// active engine.
#[allow(unused_unsafe)]
pub unsafe fn get_atom<'a, F, R>(term: &Term<'a>, func: F) -> PrologResult<R>
where
    F: Fn(Option<&Atom>) -> R,
{
    let mut atom = 0;
    let result = unsafe { PL_get_atom(term.term_ptr(), &mut atom) };

    if unsafe { PL_exception(0) != 0 } {
        return Err(PrologError::Exception);
    }

    let arg = if result == 0 {
        None
    } else {
        let atom = unsafe { Atom::wrap(atom) };

        Some(atom)
    };

    let result = func(arg.as_ref());
    // prevent destructor from running since we never increased the refcount
    std::mem::forget(arg);

    Ok(result)
}

term_getable! {
    (Atom, term) => {
        match term.get_atom(|a| a.map(|a|a.clone())) {
            Ok(r) => r,
            // ignore this error - it'll be picked up again by the wrapper
            Err(_) => None
        }
    }
}

term_putable! {
    (self:Atom, term) => {
        unsafe { PL_put_atom(term.term_ptr(), self.atom); }
    }
}

/// A type that allows easy conversion of strings from and to an atom.
pub enum Atomable<'a> {
    Str(&'a str),
    String(String),
}

impl<'a> From<&'a str> for Atomable<'a> {
    fn from(s: &str) -> Atomable {
        Atomable::Str(s)
    }
}

impl<'a> From<String> for Atomable<'a> {
    fn from(s: String) -> Atomable<'static> {
        Atomable::String(s)
    }
}

impl<'a> Atomable<'a> {
    /// Create a new Atomable out of a String or an &str.
    pub fn new<T: Into<Atomable<'a>>>(s: T) -> Self {
        s.into()
    }

    /// Return the name.
    pub fn name(&self) -> &str {
        match self {
            Self::Str(s) => s,
            Self::String(s) => &s,
        }
    }

    /// Convert this Atomable into a new Atomable which is guaranteed to own its data.
    pub fn owned(&self) -> Atomable<'static> {
        match self {
            Self::Str(s) => Atomable::String(s.to_string()),
            Self::String(s) => Atomable::String(s.clone()),
        }
    }
}

/// Wrapper for `Atomable::new`.
pub fn atomable<'a, T: Into<Atomable<'a>>>(s: T) -> Atomable<'a> {
    Atomable::new(s)
}

/// Trait for types which can be turned into an `Atom`.
pub trait IntoAtom {
    /// Turn this object into an `Atom`.
    fn into_atom(self) -> Atom;
}

impl IntoAtom for Atom {
    fn into_atom(self) -> Atom {
        self
    }
}

impl IntoAtom for &Atom {
    fn into_atom(self) -> Atom {
        self.clone()
    }
}

impl<'a> IntoAtom for &Atomable<'a> {
    fn into_atom(self) -> Atom {
        Atom::new(self.as_ref())
    }
}

impl<'a> IntoAtom for Atomable<'a> {
    fn into_atom(self) -> Atom {
        (&self).into_atom()
    }
}

impl<'a> IntoAtom for &'a str {
    fn into_atom(self) -> Atom {
        Atom::new(self)
    }
}

/// Trait for types which can be turned into an `Atom` from a borrow.
pub trait AsAtom {
    /// Turn the borrowed object into an `Atom`.
    ///
    /// The second argument ensures that this function is called in a
    /// context where atoms are allowed to be created.
    fn as_atom(&self) -> Atom;
}

impl AsAtom for Atom {
    fn as_atom(&self) -> Atom {
        self.clone()
    }
}

impl<'a> AsAtom for Atomable<'a> {
    fn as_atom(&self) -> Atom {
        self.into_atom()
    }
}

impl AsAtom for str {
    fn as_atom(&self) -> Atom {
        self.into_atom()
    }
}

unifiable! {
    (self:Atomable<'a>, term) => {
        let result = unsafe {
            PL_unify_chars(
                term.term_ptr(),
                (PL_ATOM | REP_UTF8).try_into().unwrap(),
                self.name().len().try_into().unwrap(),
                self.name().as_bytes().as_ptr() as *const c_char,
            )
        };

        result != 0
    }
}

/// Get an atomable out of a term.
///
/// This is very much like `get_atom`, but instead of retrieving the
/// atom, we retrieve the atom's name as an &str, wrapped by an
/// `Atomable`. This means the atom reference count does not have to
/// be manipulated, and it should be slightly faster than first
/// getting the atom and then extracting its name.
pub fn get_atomable<'a, F, R>(term: &Term<'a>, func: F) -> PrologResult<R>
where
    F: Fn(Option<&Atomable>) -> R,
{
    assert_some_engine_is_active();
    let mut ptr = std::ptr::null_mut();
    let mut len = 0;
    let result = unsafe {
        PL_get_nchars(
            term.term_ptr(),
            &mut len,
            &mut ptr,
            (CVT_ATOM | REP_UTF8).try_into().unwrap(),
        )
    };

    if unsafe { PL_exception(0) != 0 } {
        return Err(PrologError::Exception);
    }

    let arg = if result == 0 {
        None
    } else {
        let swipl_string_ref =
            unsafe { std::slice::from_raw_parts(ptr as *const u8, len as usize) };

        let swipl_string = std::str::from_utf8(swipl_string_ref).unwrap();
        let atomable = Atomable::new(swipl_string);

        Some(atomable)
    };

    let result = func(arg.as_ref());
    // prevent destructor from running since we never increased the refcount
    std::mem::forget(arg);

    Ok(result)
}

term_getable! {
    (Atomable<'static>, term) => {
        match get_atomable(term, |a|a.map(|a|a.owned())) {
            Ok(r) => r,
            // ignore error - it'll be picked up in the wrapper
            Err(_) => None
        }
    }
}

term_putable! {
    (self:Atomable<'a>, term) => {
        unsafe {
            PL_put_chars(
                term.term_ptr(),
                (PL_ATOM | REP_UTF8).try_into().unwrap(),
                self.name().len().try_into().unwrap(),
                self.name().as_bytes().as_ptr() as *const c_char,
            );
        }
    }
}

impl<'a> AsRef<str> for Atomable<'a> {
    fn as_ref(&self) -> &str {
        self.name()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::*;
    #[test]
    fn create_atom_and_retrieve_name() {
        let engine = Engine::new();
        let _activation = engine.activate();

        let atom = Atom::new("the cow says moo");
        let name = atom.name();

        assert_eq!(name, "the cow says moo");
    }
    #[test]
    fn create_and_compare_some_atoms() {
        let engine = Engine::new();
        let _activation = engine.activate();

        let a1 = Atom::new("foo");
        let a2 = Atom::new("bar");
        assert!(a1 != a2);
        let a3 = Atom::new("foo");
        assert_eq!(a1, a3);
    }

    #[test]
    fn clone_atom() {
        let engine = Engine::new();
        let _activation = engine.activate();

        let a1 = Atom::new("foo");
        let a2 = a1.clone();

        assert_eq!(a1, a2);
    }

    #[test]
    fn create_atom_of_magic_length() {
        let engine = Engine::new();
        let _activation = engine.activate();

        let len = std::mem::size_of::<usize>() - 1;
        let name = (0..len).map(|_| "a").collect::<String>();

        let _atom = Atom::new(&name);
    }

    #[test]
    fn unify_atoms() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let a1 = Atom::new("foo");
        let a2 = Atom::new("bar");

        let term = context.new_term_ref();

        assert!(term.unify(&a1).is_ok());
        assert!(term.unify(a1).is_ok());
        assert!(!term.unify(a2).is_ok());
    }

    #[test]
    fn unify_atoms_from_string() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let a1 = Atom::new("foo");
        let a2 = Atom::new("bar");

        let term = context.new_term_ref();

        assert!(term.unify(atomable("foo")).is_ok());
        assert!(term.unify(atomable("foo")).is_ok());
        assert!(term.unify(a1).is_ok());
        assert!(!term.unify(atomable("bar")).is_ok());
        assert!(!term.unify(a2).is_ok());
    }

    #[test]
    fn unify_from_atomable_turned_atom() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let a1 = atomable("foo").as_atom();
        let a2 = atomable("bar").as_atom();

        assert_eq!("foo", a1.name());

        let term = context.new_term_ref();

        assert!(term.unify(&a1).is_ok());
        assert!(term.unify(&a1).is_ok());
        assert!(!term.unify(&a2).is_ok());
    }

    #[test]
    fn retrieve_atom_temporarily() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let a1 = "foo".as_atom();
        let term = context.new_term_ref();
        term.unify(&a1).unwrap();
        term.get_atom(|a2| assert_eq!(&a1, a2.unwrap())).unwrap();
    }

    #[test]
    fn retrieve_atom() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let a1 = "foo".as_atom();
        let term = context.new_term_ref();
        term.unify(&a1).unwrap();
        let a2: Atom = term.get().unwrap();

        assert_eq!(a1, a2);
    }

    #[test]
    fn retrieve_atomable_temporarily() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let a1 = "foo".as_atom();
        let term = context.new_term_ref();
        term.unify(&a1).unwrap();
        term.get_atom_name(|a2| assert_eq!("foo", a2.unwrap()))
            .unwrap();
    }

    #[test]
    fn retrieve_atomable() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let a1 = "foo".as_atom();
        let term = context.new_term_ref();
        term.unify(&a1).unwrap();
        let a2: Atomable = term.get().unwrap();

        assert_eq!("foo", a2.name());
    }
}
