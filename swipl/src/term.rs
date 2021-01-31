use super::atom::*;
use super::context::*;
use std::convert::TryInto;
use std::fmt::Debug;
use std::os::raw::c_char;
use swipl_sys::*;

use std::fmt;

#[derive(Clone)]
pub struct Term<'a> {
    term: term_t,
    context: &'a dyn TermOrigin,
}

impl<'a> Debug for Term<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(fmt, "Term({:?})", self.term)
    }
}

impl<'a> Term<'a> {
    pub unsafe fn new(term: term_t, context: &'a dyn TermOrigin) -> Self {
        Term { term, context }
    }

    pub fn term_ptr(&self) -> term_t {
        self.term
    }

    pub fn assert_term_handling_possible(&self) {
        if !self.context.is_engine_active() {
            panic!("term is not part of the active engine");
        }
    }

    pub fn unify<U: Unifiable>(&self, unifiable: U) -> SemidetResult {
        unifiable.unify(self)
    }

    pub fn unify_arg<U: Unifiable>(&self, index: usize, unifiable: U) -> SemidetResult {
        if index == 0 {
            panic!("unify_arg was given index 0, but index starts at 1");
        }

        self.assert_term_handling_possible();

        let arg_ref = unsafe { PL_new_term_ref() };

        let result = unsafe { PL_get_arg(index.try_into().unwrap(), self.term, arg_ref) };
        let arg = unsafe { Term::new(arg_ref, self.context) };
        let mut result2 = false;
        if result != 0 {
            result2 = arg.unify(unifiable)?;
        }

        unsafe { PL_reset_term_refs(arg_ref) };

        Ok(result2)
    }

    pub fn get<G: TermGetable>(&self) -> Option<G> {
        G::get(self)
    }

    pub fn get_arg<G: TermGetable>(&self, index: usize) -> Option<G> {
        if index == 0 {
            panic!("unify_arg was given index 0, but index starts at 1");
        }

        self.assert_term_handling_possible();

        let arg_ref = unsafe { PL_new_term_ref() };

        let result = unsafe { PL_get_arg(index.try_into().unwrap(), self.term, arg_ref) };
        let arg = unsafe { Term::new(arg_ref, self.context) };
        let mut result2 = None;
        if result != 0 {
            result2 = arg.get();
        }

        unsafe { PL_reset_term_refs(arg_ref) };

        result2
    }

    pub fn get_str<R, F>(&self, func: F) -> R
    where
        F: Fn(Option<&str>) -> R,
    {
        self.assert_term_handling_possible();
        let mut ptr = std::ptr::null_mut();
        let mut len = 0;
        let result = unsafe {
            PL_get_nchars(
                self.term,
                &mut len,
                &mut ptr,
                (CVT_STRING | REP_UTF8).try_into().unwrap(),
            )
        };
        let arg = if result == 0 {
            None
        } else {
            let swipl_string_ref =
                unsafe { std::slice::from_raw_parts(ptr as *const u8, len as usize) };

            let swipl_string = std::str::from_utf8(swipl_string_ref).unwrap();

            Some(swipl_string)
        };

        func(arg)
    }

    pub fn get_atom<R, F>(&self, func: F) -> R
    where
        F: Fn(Option<&Atom>) -> R,
    {
        self.assert_term_handling_possible();
        unsafe { get_atom(self, func) }
    }

    pub fn get_atomable<R, F>(&self, func: F) -> R
    where
        F: Fn(Option<&Atomable>) -> R,
    {
        self.assert_term_handling_possible();
        unsafe { get_atomable(self, func) }
    }
}

pub trait TermOrigin {
    fn origin_engine_ptr(&self) -> PL_engine_t;
    fn is_engine_active(&self) -> bool;
}

/// Trait for term unification.
///
/// This is marked unsafe because in order to do term unification, we
/// must be sure that
/// - the term is created on the engine which is currently active
/// - the given context is a context for this engine
///
/// Not checking those preconditions results in undefined
/// behavior. Therefore, care must be taken to ensure that `unify` is
/// actually safe.
///
/// The macro `unifiable` provides a way to safely implement this trait.
pub unsafe trait Unifiable {
    fn unify(&self, term: &Term) -> SemidetResult;
}

unsafe impl<T: Unifiable> Unifiable for &T {
    fn unify(&self, term: &Term) -> SemidetResult {
        (*self).unify(term)
    }
}

pub unsafe trait TermGetable: Sized {
    fn get(term: &Term) -> Option<Self>;
}

#[macro_export]
macro_rules! unifiable {
    (($self_:ident : $t:ty, $term_: ident) => $b: block) => {
        // unsafe justification: this macro inserts an assert in front
        // of the unification body, to ensure that we are given a term
        // that matches the given context, and that the currently
        // activated engine is one for which this term was created.
        unsafe impl<'a> Unifiable for $t {
            fn unify(&$self_, $term_: &Term) -> SemidetResult {
                $term_.assert_term_handling_possible();

                $b
            }
        }
    }
}

#[macro_export]
macro_rules! term_getable {
    (($t:ty, $term_: ident) => $b: block) => {
        // unsafe justification: this macro inserts an assert in front
        // of the term get body, to ensure that we are given a term
        // that matches the given context, and that the currently
        // activated engine is one for which this term was created.
        unsafe impl<'a> TermGetable for $t {
            fn get($term_: &Term) -> Option<Self> {
                $term_.assert_term_handling_possible();

                $b
            }
        }
    };
}

unifiable! {
    (self:Term<'a>, term) => {
        if self.context.origin_engine_ptr() != term.context.origin_engine_ptr() {
            panic!("terms being unified are not part of the same engine");
        }

        // unsafe justification: the fact that we have terms here means we are dealing with some kind of active context, and therefore an initialized swipl. The check above has made sure that both terms are part of the same engine too, and the unifiable! macro takes care of checking that we're on the correct engine.
        let result = unsafe { PL_unify(self.term, term.term) };

        // TODO we should actually properly test for an exception here.
        Ok(result != 0)
    }
}

unifiable! {
    (self:bool, term) => {
        let num = match self {
            true => 1,
            false => 0,
        };
        let result = unsafe { PL_unify_bool(term.term, num) };

        Ok(result != 0)
    }
}

term_getable! {
    (bool, term) => {
        let mut out = 0;
        let result = unsafe { PL_get_bool(term.term, &mut out) };
        if result == 0 {
            None
        }
        else {
            Some(out != 0)
        }
    }
}

unifiable! {
    (self:u64, term) => {
        let result = unsafe { PL_unify_uint64(term.term, *self) };

        Ok(result != 0)
    }
}

term_getable! {
    (u64, term) => {
        let mut out = 0;
        let result = unsafe { PL_cvt_i_uint64(term.term, &mut out) };
        if result == 0 {
            None
        }
        else {
            Some(out)
        }
    }
}

unifiable! {
    (self:i64, term) => {
        let result = unsafe { PL_unify_int64(term.term, *self) };

        Ok(result != 0)
    }
}

term_getable! {
    (i64, term) => {
        let mut out = 0;
        let result = unsafe { PL_cvt_i_int64(term.term, &mut out) };
        if result == 0 {
            None
        }
        else {
            Some(out)
        }
    }
}

unifiable! {
    (self:f64, term) => {
        let result = unsafe { PL_unify_float(term.term, *self) };

        Ok(result != 0)
    }
}

term_getable! {
    (f64, term) => {
        let mut out = 0.0;
        let result = unsafe { PL_get_float(term.term, &mut out) };
        if result == 0 {
            None
        }
        else {
            Some(out)
        }
    }
}

unifiable! {
    (self:&str, term) => {
        let result = unsafe { PL_unify_chars(
            term.term_ptr(),
            (PL_STRING | REP_UTF8).try_into().unwrap(),
            self.len().try_into().unwrap(),
            self.as_bytes().as_ptr() as *const c_char,
        )
        };

        Ok(result != 0)
    }
}

term_getable! {
    (String, term) => {
        term.get_str(|s|s.map(|s|s.to_owned()))
    }
}

pub struct Nil;
unifiable! {
    (self:Nil, term) => {
        let result = unsafe { PL_unify_nil(term.term_ptr()) };

        Ok(result != 0)
    }
}

term_getable! {
    (Nil, term) => {
        let result = unsafe { PL_get_nil(term.term_ptr()) };

        match result != 0 {
            true => Some(Nil),
            false => None
        }
    }
}

unsafe impl<'a, T> Unifiable for &'a [T]
where
    &'a T: 'static + Unifiable,
{
    fn unify(&self, term: &Term) -> SemidetResult {
        term.assert_term_handling_possible();
        // let's create a fake context so we can make a frame
        // unsafe justification: This context will only exist inside this implementation. We know we are in some valid context for term handling, so that's great.
        let context = unsafe { unmanaged_engine_context() };

        let frame = context.open_frame();
        let list = frame.new_term_ref();
        list.unify(term)?;
        let mut success = true;

        for t in self.iter() {
            // create a new frame to ensure we don't just keep putting head and tail refs on the stack.
            let frame2 = frame.open_frame();
            let head = frame2.new_term_ref();
            let tail = frame2.new_term_ref();
            success =
                unsafe { PL_unify_list(list.term_ptr(), head.term_ptr(), tail.term_ptr()) != 0 };

            if !success {
                break;
            }

            success = head.unify(t)?;

            // reset term - should really be a method on term
            unsafe { PL_put_variable(list.term_ptr()) };

            list.unify(tail)?;
            frame2.close_frame();
        }

        if success {
            success = unsafe { PL_unify_nil(list.term_ptr()) != 0 };
            frame.close_frame();
        }

        Ok(success)
    }
}

unsafe impl<T: TermGetable> TermGetable for Vec<T> {
    fn get(term: &Term) -> Option<Self> {
        term.assert_term_handling_possible();

        let mut result: Vec<T> = Vec::new();

        // let's create a fake context so we can make a frame
        // unsafe justification: This context will only exist inside this implementation. We know we are in some valid context for term handling, so that's great.
        let context = unsafe { unmanaged_engine_context() };

        let frame = context.open_frame();
        let list = frame.new_term_ref();
        list.unify(term).unwrap();
        let mut success = true;
        loop {
            if unsafe { PL_get_nil(list.term_ptr()) != 0 } {
                break;
            }

            let frame2 = frame.open_frame();
            let head = frame2.new_term_ref();
            let tail = frame2.new_term_ref();
            success =
                unsafe { PL_get_list(list.term_ptr(), head.term_ptr(), tail.term_ptr()) != 0 };

            if !success {
                break;
            }

            let elt = head.get();
            if elt.is_none() {
                success = false;
                break;
            }

            result.push(elt.unwrap());

            // reset term - should really be a method on term
            unsafe { PL_put_variable(list.term_ptr()) };
            list.unify(tail).unwrap();
            frame2.close_frame();
        }

        frame.close_frame();

        match success {
            true => Some(result),
            false => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::context::*;
    use crate::engine::*;
    #[test]
    fn unify_some_terms_with_success() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = context.new_term_ref();
        let term2 = context.new_term_ref();
        assert!(term1.unify(42_u64).unwrap());
        assert!(term2.unify(42_u64).unwrap());
        assert!(term1.unify(&term2).unwrap());
    }

    #[test]
    fn unify_some_terms_with_failure() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = context.new_term_ref();
        let term2 = context.new_term_ref();
        assert!(term1.unify(42_u64).unwrap());
        assert!(term2.unify(43_u64).unwrap());
        assert!(!term1.unify(&term2).unwrap());
    }

    #[test]
    fn unify_twice_different_failure() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.new_term_ref();
        assert!(term.unify(42_u64).unwrap());
        assert!(!term.unify(43_u64).unwrap());
    }

    #[test]
    fn unify_twice_different_with_rewind_success() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();
        let term = context.new_term_ref();
        let context2 = context.open_frame();

        assert!(term.unify(42_u64).unwrap());
        context2.rewind_frame();
        assert!(term.unify(43_u64).unwrap());
    }

    #[test]
    fn unify_and_get_bools() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = context.new_term_ref();
        assert!(term1.get::<bool>().is_none());
        term1.unify(true).unwrap();
        assert_eq!(Some(true), term1.get::<bool>());
        let term2 = context.new_term_ref();
        term2.unify(false).unwrap();
        assert_eq!(Some(false), term2.get::<bool>());
    }

    #[test]
    fn unify_and_get_u64s() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = context.new_term_ref();
        assert!(term1.get::<u64>().is_none());
        term1.unify(42_u64).unwrap();
        assert_eq!(Some(42), term1.get::<u64>());
        let term2 = context.new_term_ref();
        term2.unify(0xffffffff_u64).unwrap();
        assert_eq!(Some(0xffffffff), term2.get::<u64>());
        let term3 = context.new_term_ref();
        term3.unify(0xffffffffffffffff_u64).unwrap();
        assert_eq!(Some(0xffffffffffffffff), term3.get::<u64>());
    }

    #[test]
    fn unify_and_get_string_refs() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = context.new_term_ref();
        term1.get_str(|s| assert!(s.is_none()));
        term1.unify("hello there").unwrap();
        term1.get_str(|s| assert_eq!("hello there", s.unwrap()));
    }

    #[test]
    fn unify_and_get_strings() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = context.new_term_ref();
        assert!(term1.get::<String>().is_none());
        term1.unify("hello there").unwrap();
        assert_eq!("hello there", term1.get::<String>().unwrap());
    }

    #[test]
    fn unify_and_get_different_types_fails() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = context.new_term_ref();
        term1.unify(42_u64).unwrap();
        assert_eq!(None, term1.get::<bool>());
    }

    #[test]
    fn unify_list() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.new_term_ref();
        assert!(term.unify([42_u64, 12, 3, 0, 5].as_ref()).unwrap());

        assert_eq!(
            [42_u64, 12, 3, 0, 5].as_ref(),
            term.get::<Vec<u64>>().unwrap()
        );
    }
}
