use super::context::*;
use super::term::*;
use crate::unifiable;
use std::borrow::Cow;
use std::convert::TryInto;
use std::os::raw::c_char;
use swipl_sys::*;

#[derive(PartialEq, Eq, Debug)]
pub struct Atom {
    atom: atom_t,
}

impl Atom {
    pub unsafe fn new(atom: atom_t) -> Atom {
        Atom { atom }
    }

    pub fn name<'a, T: ContextType>(&'a self, _context: &Context<'a, T>) -> &'a str {
        // TODO we're just assuming that what we get out of prolog is utf-8. but it's not. On windows, ad ifferent encoding is used and it is unclear to me if they convert to utf8 just for this call. Need to check.

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
    (self:&Atom, _context, term) => {
        let result = unsafe { PL_unify_atom(term.term_ptr(), self.atom) };

        return result != 0;
    }
}

unifiable! {
    (self:Atom, context, term) => {
        (&self).unify(context, term)
    }
}

pub struct Atomable<'a> {
    name: Cow<'a, str>,
}

impl<'a> Atomable<'a> {
    pub fn new<T: Into<Cow<'a, str>>>(s: T) -> Self {
        Self { name: s.into() }
    }

    pub fn as_atom<T: ContextType>(&self, context: &Context<T>) -> Atom {
        context.atom_from_atomable(self)
    }
}

pub fn atomable<'a, T: Into<Cow<'a, str>>>(s: T) -> Atomable<'a> {
    Atomable::new(s)
}

unifiable! {
    (self:&Atomable<'a>, context, term) => {
        let result = unsafe {
            PL_unify_chars(
                term.term_ptr(),
                (PL_ATOM | REP_UTF8).try_into().unwrap(),
                self.name.len().try_into().unwrap(),
                self.name.as_bytes().as_ptr() as *const c_char,
            )
        };

        return result != 0;
    }
}

unifiable! {
    (self:Atomable<'a>, context, term) => {
        (&self).unify(context, term)
    }
}

impl<'a> AsRef<str> for Atomable<'a> {
    fn as_ref(&self) -> &str {
        self.name.as_ref()
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

        assert!(term.unify(&a1));
        assert!(term.unify(a1));
        assert!(!term.unify(a2));
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

        assert!(term.unify(atomable("foo")));
        assert!(term.unify(atomable("foo")));
        assert!(term.unify(a1));
        assert!(!term.unify(atomable("bar")));
        assert!(!term.unify(a2));
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

        assert!(term.unify(&a1));
        assert!(term.unify(&a1));
        assert!(!term.unify(&a2));
    }
}
