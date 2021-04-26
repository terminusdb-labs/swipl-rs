use super::context::*;
use super::fli::*;
use super::term::*;
use crate::{term_getable, term_putable, unifiable};
use std::convert::TryInto;
use std::os::raw::c_char;

#[derive(PartialEq, Eq, Debug)]
pub struct Atom {
    atom: atom_t,
}

impl Atom {
    pub unsafe fn wrap(atom: atom_t) -> Atom {
        Atom { atom }
    }

    pub unsafe fn new(name: &str) -> Atom {
        // there's a worrying bit of information in the documentation.
        // It says that in some cases for small strings,
        // PL_new_atom_mbchars will recalculate the size of the string
        // using strlen. In that case we need to give it a
        // nul-terminated string.
        const S_USIZE: usize = std::mem::size_of::<usize>();
        let atom = if name.len() == S_USIZE - 1 {
            let mut buf: [u8; S_USIZE] = [0; S_USIZE];
            buf[..name.len()].clone_from_slice(name.as_bytes());

            PL_new_atom_mbchars(
                REP_UTF8.try_into().unwrap(),
                name.len().try_into().unwrap(),
                buf.as_ptr() as *const c_char,
            )
        } else {
            PL_new_atom_mbchars(
                REP_UTF8.try_into().unwrap(),
                name.len().try_into().unwrap(),
                name.as_ptr() as *const c_char,
            )
        };

        Atom::wrap(atom)
    }

    pub fn atom_ptr(&self) -> atom_t {
        self.atom
    }

    pub fn name<P: ActiveEnginePromise>(&self, _: &P) -> &str {
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
        unsafe { PL_register_atom(self.atom) };
        Atom { atom: self.atom }
    }
}

impl Drop for Atom {
    fn drop(&mut self) {
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

#[allow(unused_unsafe)]
pub unsafe fn get_atom<'a, F, R>(term: &Term<'a>, func: F) -> R
where
    F: Fn(Option<&Atom>) -> R,
{
    let mut atom = 0;
    let result = unsafe { PL_get_atom(term.term_ptr(), &mut atom) };

    let arg = if result == 0 {
        None
    } else {
        let atom = unsafe { Atom::wrap(atom) };

        Some(atom)
    };

    let result = func(arg.as_ref());
    // prevent destructor from running since we never increased the refcount
    std::mem::forget(arg);

    result
}

term_getable! {
    (Atom, term) => {
        term.get_atom(|a| a.map(|a|a.clone()))
    }
}

term_putable! {
    (self:Atom, term) => {
        unsafe { PL_put_atom(term.term_ptr(), self.atom); }
    }
}

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
    pub fn new<T: Into<Atomable<'a>>>(s: T) -> Self {
        s.into()
    }

    pub fn name(&self) -> &str {
        match self {
            Self::Str(s) => s,
            Self::String(s) => &s,
        }
    }

    pub fn owned(&self) -> Atomable<'static> {
        match self {
            Self::Str(s) => Atomable::String(s.to_string()),
            Self::String(s) => Atomable::String(s.clone()),
        }
    }
}

pub fn atomable<'a, T: Into<Atomable<'a>>>(s: T) -> Atomable<'a> {
    Atomable::new(s)
}

pub trait IntoAtom {
    fn into_atom<P: ActiveEnginePromise>(self, promise: &P) -> Atom;

    unsafe fn into_atom_unsafe(self) -> Atom
    where
        Self: Sized,
    {
        let promise = UnsafeActiveEnginePromise::new();
        self.into_atom(&promise)
    }
}

impl IntoAtom for Atom {
    fn into_atom<P: ActiveEnginePromise>(self, _: &P) -> Atom {
        self
    }
}

impl IntoAtom for &Atom {
    fn into_atom<P: ActiveEnginePromise>(self, _: &P) -> Atom {
        self.clone()
    }
}

impl<'a> IntoAtom for &Atomable<'a> {
    fn into_atom<P: ActiveEnginePromise>(self, _: &P) -> Atom {
        // unsafe justification: with an active engine, it is safe to create atoms
        unsafe { Atom::new(self.as_ref()) }
    }
}

impl<'a> IntoAtom for Atomable<'a> {
    fn into_atom<P: ActiveEnginePromise>(self, promise: &P) -> Atom {
        (&self).into_atom(promise)
    }
}

impl<'a> IntoAtom for &'a str {
    fn into_atom<P: ActiveEnginePromise>(self, _: &P) -> Atom {
        // unsafe justification: with an active engine, it is safe to create atoms
        unsafe { Atom::new(self) }
    }
}

pub trait AsAtom {
    fn as_atom<P: ActiveEnginePromise>(&self, promise: &P) -> Atom;
}

impl AsAtom for Atom {
    fn as_atom<P: ActiveEnginePromise>(&self, _: &P) -> Atom {
        self.clone()
    }
}

impl<'a> AsAtom for Atomable<'a> {
    fn as_atom<P: ActiveEnginePromise>(&self, promise: &P) -> Atom {
        self.into_atom(promise)
    }
}

impl AsAtom for str {
    fn as_atom<P: ActiveEnginePromise>(&self, promise: &P) -> Atom {
        self.into_atom(promise)
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

#[allow(unused_unsafe)]
pub unsafe fn get_atomable<'a, F, R>(term: &Term<'a>, func: F) -> R
where
    F: Fn(Option<&Atomable>) -> R,
{
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

    result
}

term_getable! {
    (Atomable<'static>, term) => {
        term.get_atomable(|a|a.map(|a|a.owned()))
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
    use crate::engine::*;
    #[test]
    fn create_atom_and_retrieve_name() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let atom = context.new_atom("the cow says moo");
        let name = atom.name(&context);

        assert_eq!(name, "the cow says moo");
    }
    #[test]
    fn create_and_compare_some_atoms() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let a1 = context.new_atom("foo");
        let a2 = context.new_atom("bar");
        assert!(a1 != a2);
        let a3 = context.new_atom("foo");
        assert_eq!(a1, a3);
    }

    #[test]
    fn clone_atom() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let a1 = context.new_atom("foo");
        let a2 = a1.clone();

        assert_eq!(a1, a2);
    }

    #[test]
    fn create_atom_of_magic_length() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let len = std::mem::size_of::<usize>() - 1;
        let name = (0..len).map(|_| "a").collect::<String>();

        let _atom = context.new_atom(&name);
    }

    #[test]
    fn unify_atoms() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let a1 = context.new_atom("foo");
        let a2 = context.new_atom("bar");

        let term = context.new_term_ref();

        assert!(term.unify(&a1).is_ok());
        assert!(term.unify(a1).is_ok());
        assert!(!term.unify(a2).is_ok());
    }

    #[test]
    fn unify_atoms_from_string() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let a1 = context.new_atom("foo");
        let a2 = context.new_atom("bar");

        let term = context.new_term_ref();

        assert!(term.unify(atomable("foo")).is_ok());
        assert!(term.unify(atomable("foo")).is_ok());
        assert!(term.unify(a1).is_ok());
        assert!(!term.unify(atomable("bar")).is_ok());
        assert!(!term.unify(a2).is_ok());
    }

    #[test]
    fn unify_from_atomable_turned_atom() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let a1 = atomable("foo").as_atom(&context);
        let a2 = atomable("bar").as_atom(&context);

        assert_eq!("foo", a1.name(&context));

        let term = context.new_term_ref();

        assert!(term.unify(&a1).is_ok());
        assert!(term.unify(&a1).is_ok());
        assert!(!term.unify(&a2).is_ok());
    }

    #[test]
    fn retrieve_atom_temporarily() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let a1 = "foo".as_atom(&context);
        let term = context.new_term_ref();
        term.unify(&a1).unwrap();
        term.get_atom(|a2| assert_eq!(&a1, a2.unwrap()));
    }

    #[test]
    fn retrieve_atom() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let a1 = "foo".as_atom(&context);
        let term = context.new_term_ref();
        term.unify(&a1).unwrap();
        let a2: Atom = term.get().unwrap().unwrap();

        assert_eq!(a1, a2);
    }

    #[test]
    fn retrieve_atomable_temporarily() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let a1 = "foo".as_atom(&context);
        let term = context.new_term_ref();
        term.unify(&a1).unwrap();
        term.get_atomable(|a2| assert_eq!("foo", a2.unwrap().name()));
    }

    #[test]
    fn retrieve_atomable() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let a1 = "foo".as_atom(&context);
        let term = context.new_term_ref();
        term.unify(&a1).unwrap();
        let a2: Atomable = term.get().unwrap().unwrap();

        assert_eq!("foo", a2.name());
    }
}
