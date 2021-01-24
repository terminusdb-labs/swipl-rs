use super::atom::*;
use super::consts::*;
use super::context::*;
use super::term::*;
use crate::{term_getable, unifiable};
use std::convert::TryInto;
use swipl_sys::*;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Functor {
    functor: functor_t,
}

impl Functor {
    pub unsafe fn wrap(functor: functor_t) -> Self {
        Self { functor }
    }

    pub unsafe fn new<A: IntoAtom>(name: A, arity: u16) -> Functor {
        if arity as usize > MAX_ARITY {
            panic!("functor arity is >1024: {}", arity);
        }
        let atom = name.into_atom_unsafe();

        let functor = PL_new_functor(atom.atom_ptr(), arity.try_into().unwrap());

        Functor::wrap(functor)
    }

    pub fn functor_ptr(&self) -> functor_t {
        self.functor
    }

    pub fn with_name<P: ActiveEnginePromise, F, R>(&self, _: &P, func: F) -> R
    where
        F: Fn(&Atom) -> R,
    {
        let atom = unsafe { Atom::wrap(PL_functor_name(self.functor)) };

        let result = func(&atom);

        std::mem::forget(atom);

        result
    }

    pub fn name<P: ActiveEnginePromise>(&self, promise: &P) -> Atom {
        self.with_name(promise, |n| n.clone())
    }

    pub fn name_string<P: ActiveEnginePromise>(&self, promise: &P) -> String {
        self.with_name(promise, |n| n.name(promise).to_string())
    }

    pub fn with_name_string<P: ActiveEnginePromise, F, R>(&self, promise: &P, func: F) -> R
    where
        F: Fn(&str) -> R,
    {
        self.with_name(promise, |n| func(n.name(promise)))
    }

    pub fn arity<P: ActiveEnginePromise>(&self, _: &P) -> u16 {
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

    pub unsafe fn as_functor_unsafe<'b>(&self) -> Functor {
        Functor::new(&self.name, self.arity)
    }

    pub fn as_functor<'b, T: ContextType>(&self, context: &Context<'b, T>) -> Functor {
        context.new_functor(&self.name, self.arity)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::*;

    #[test]
    fn create_and_query_functor() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let f = context.new_functor("moocows", 3);

        assert_eq!("moocows", f.name_string(&context));
        assert_eq!("moocows", f.name(&context).name(&context));
        f.with_name(&context, |name| assert_eq!("moocows", name.name(&context)));
        f.with_name_string(&context, |name| assert_eq!("moocows", name));

        assert_eq!(3, f.arity(&context));
    }

    #[test]
    fn unify_same_functor_twice_succeeds() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let f = context.new_functor("moocows", 3);
        let term = context.new_term_ref();
        assert!(term.unify(&f));
        assert!(term.unify(&f));
    }

    #[test]
    fn unity_retrieve_same_functor() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let f = context.new_functor("moocows", 3);
        let term = context.new_term_ref();
        assert!(term.unify(&f));
    }

    #[test]
    fn unify_different_functor_arity_fails() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let f1 = context.new_functor("moocows", 3);
        let term = context.new_term_ref();
        term.unify(&f1);
        let f2: Functor = term.get().unwrap();
        assert_eq!(f1, f2);
    }

    #[test]
    fn unify_different_functor_name_fails() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let f1 = context.new_functor("moocows", 3);
        let f2 = context.new_functor("oinkpigs", 3);
        let term = context.new_term_ref();
        assert!(term.unify(&f1));
        assert!(!term.unify(&f2));
    }

    #[test]
    #[should_panic]
    fn functor_creation_with_too_high_arity_panics() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let _f = context.new_functor("moocows", 1025);
    }

    #[test]
    fn functor_arg_unify_and_get_succeeds() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let f = context.new_functor("moocows", 2);
        let term = context.new_term_ref();
        assert_eq!(None, term.get_arg::<u64>(1));
        assert!(term.unify(f));
        assert_eq!(None, term.get_arg::<u64>(1));
        assert!(term.unify_arg(1, 42_u64));
        assert_eq!(Some(42_u64), term.get_arg(1));
        assert!(term.unify_arg(1, 42_u64));
        assert!(!term.unify_arg(1, 43_u64));

        assert!(term.unify_arg(2, 24_u64));
        assert_eq!(Some(24_u64), term.get_arg(2));

        assert!(!term.unify_arg(3, 24_u64));
        assert_eq!(None, term.get_arg::<u64>(3));
    }
}
