use super::atom::*;
use super::consts::*;
use super::engine::*;
use super::fli::*;
use super::term::*;

use std::convert::TryInto;

use crate::{term_getable, term_putable, unifiable};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Functor {
    functor: functor_t,
}

impl Functor {
    pub unsafe fn wrap(functor: functor_t) -> Self {
        Self { functor }
    }

    pub fn new<A: IntoAtom>(name: A, arity: u16) -> Functor {
        assert_some_engine_is_active();
        if arity as usize > MAX_ARITY {
            panic!("functor arity is >1024: {}", arity);
        }
        let atom = name.into_atom();

        let functor = unsafe { PL_new_functor(atom.atom_ptr(), arity.try_into().unwrap()) };

        unsafe { Functor::wrap(functor) }
    }

    pub fn functor_ptr(&self) -> functor_t {
        self.functor
    }

    pub fn with_name<F, R>(&self, func: F) -> R
    where
        F: Fn(&Atom) -> R,
    {
        let atom = unsafe { Atom::wrap(PL_functor_name(self.functor)) };

        let result = func(&atom);

        std::mem::forget(atom);

        result
    }

    pub fn name(&self) -> Atom {
        self.with_name(|n| n.clone())
    }

    pub fn name_string(&self) -> String {
        self.with_name(|n| n.name().to_string())
    }

    pub fn with_name_string<F, R>(&self, func: F) -> R
    where
        F: Fn(&str) -> R,
    {
        self.with_name(|n| func(n.name()))
    }

    pub fn arity(&self) -> u16 {
        assert_some_engine_is_active();
        let arity = unsafe { PL_functor_arity(self.functor) };

        arity.try_into().unwrap()
    }
}

unifiable! {
    (self: Functor, term) => {
        let result = unsafe {PL_unify_compound(term.term_ptr(), self.functor)};

        result != 0
    }
}

term_getable! {
    (Functor, term) => {
        let mut functor = 0;
        let result = unsafe { PL_get_functor(term.term_ptr(), &mut functor) };

        if result == 0 {
            None
        }
        else {
            Some(unsafe { Functor::wrap(functor) })
        }

    }
}

term_putable! {
    (self: Functor, term) => {
        unsafe {PL_put_functor(term.term_ptr(), self.functor)};
    }
}

pub struct Functorable<'a> {
    name: Atomable<'a>,
    arity: u16,
}

impl<'a> Functorable<'a> {
    pub fn new<A: Into<Atomable<'a>>>(name: A, arity: u16) -> Self {
        if arity as usize > MAX_ARITY {
            panic!("tried to create a functorable with arity >1024: {}", arity);
        }

        Self {
            name: name.into(),
            arity,
        }
    }

    pub fn as_functor(&self) -> Functor {
        Functor::new(&self.name, self.arity)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::*;

    #[test]
    fn create_and_query_functor() {
        let engine = Engine::new();
        let _activation = engine.activate();

        let f = Functor::new("moocows", 3);

        assert_eq!("moocows", f.name_string());
        assert_eq!("moocows", f.name().name());
        f.with_name(|name| assert_eq!("moocows", name.name()));
        f.with_name_string(|name| assert_eq!("moocows", name));

        assert_eq!(3, f.arity());
    }

    #[test]
    fn unify_same_functor_twice_succeeds() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let f = Functor::new("moocows", 3);
        let term = context.new_term_ref();
        assert!(term.unify(&f).is_ok());
        assert!(term.unify(&f).is_ok());
    }

    #[test]
    fn unity_retrieve_same_functor() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let f = Functor::new("moocows", 3);
        let term = context.new_term_ref();
        assert!(term.unify(&f).is_ok());
    }

    #[test]
    fn unify_different_functor_arity_fails() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let f1 = Functor::new("moocows", 3);
        let term = context.new_term_ref();
        term.unify(&f1).unwrap();
        let f2: Functor = term.get().unwrap();
        assert_eq!(f1, f2);
    }

    #[test]
    fn unify_different_functor_name_fails() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let f1 = Functor::new("moocows", 3);
        let f2 = Functor::new("oinkpigs", 3);
        let term = context.new_term_ref();
        assert!(term.unify(&f1).is_ok());
        assert!(!term.unify(&f2).is_ok());
    }

    #[test]
    #[should_panic]
    fn functor_creation_with_too_high_arity_panics() {
        let engine = Engine::new();
        let _activation = engine.activate();

        let _f = Functor::new("moocows", 1025);
    }

    #[test]
    fn functor_arg_unify_and_get_succeeds() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let f = Functor::new("moocows", 2);
        let term = context.new_term_ref();
        assert!(term.get_arg::<u64>(1).unwrap_err().is_failure());
        assert!(term.unify(f).is_ok());
        assert!(term.get_arg::<u64>(1).unwrap_err().is_failure());
        assert!(term.unify_arg(1, 42_u64).is_ok());
        assert_eq!(42_u64, term.get_arg(1).unwrap());
        assert!(term.unify_arg(1, 42_u64).is_ok());
        assert!(!term.unify_arg(1, 43_u64).is_ok());

        assert!(term.unify_arg(2, 24_u64).is_ok());
        assert_eq!(24_u64, term.get_arg(2).unwrap());

        assert!(!term.unify_arg(3, 24_u64).is_ok());
        assert!(term.get_arg::<u64>(3).unwrap_err().is_failure());
    }
}
