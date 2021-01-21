use super::context::*;
use swipl_sys::*;

pub struct Term<'a> {
    term: term_t,
    context: &'a dyn TermOrigin,
}

impl<'a> Term<'a> {
    pub unsafe fn new(term: term_t, context: &'a dyn TermOrigin) -> Self {
        Term { term, context }
    }

    pub fn term_ptr(&self) -> term_t {
        self.term
    }

    pub fn assert_unification_possible<T: ContextType>(&self, context: &Context<T>) {
        if !self.context.is_engine_active() {
            panic!("term is not part of an active engine");
        }

        if self.context.origin_engine_ptr() != context.engine_ptr() {
            panic!("term unification called with a context whose engine does not match this term");
        }
    }

    pub fn unify<U: Unifiable>(&self, unifiable: U) -> bool {
        // unsafe justification: we know there is a valid context, otherwise this term would not exist. We just don't care exactly what it is.
        let context = self.context.context();
        unifiable.unify(&context, self)
    }
}

pub trait TermOrigin {
    fn origin_engine_ptr(&self) -> PL_engine_t;
    fn is_engine_active(&self) -> bool;
    fn context(&self) -> Context<Unknown>;
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
    fn unify<T: ContextType>(self, context: &Context<T>, term: &Term) -> bool;
}

#[macro_export]
macro_rules! unifiable {
    (($self_:ident : $t:ty, $context_: ident, $term_: ident) => $b: block) => {
        // unsafe justification: this macro inserts an assert in front
        // of the unification body, to ensure that we are given a term
        // that matches the given context, and that the currently
        // activated engine is one for which this term was created.
        unsafe impl<'a> Unifiable for $t {
            fn unify<T:ContextType>($self_, $context_: &Context<T>, $term_: &Term) -> bool {
                $term_.assert_unification_possible($context_);

                $b
            }
        }
    }
}

unifiable! {
    (self:&Term<'a>, _context, term) => {
        if self.context.origin_engine_ptr() != term.context.origin_engine_ptr() {
            panic!("terms being unified are not part of the same engine");
        }

        // unsafe justification: the fact that we have terms here means we are dealing with some kind of active context, and therefore an initialized swipl. The checks above have made sure that both terms are part of the same engine too, and that this engine is the current engine.
        let result = unsafe { PL_unify(self.term, term.term) };

        // TODO we should actually properly test for an exception here.
        result != 0
    }
}

unifiable! {
    (self:bool, _context, term) => {
        let num = match self {
            true => 0,
            false => 1,
        };
        let result = unsafe { PL_unify_bool(term.term, num) };

        result != 0
    }
}

unifiable! {
    (self:u64, _context, term) => {
        let result = unsafe { PL_unify_uint64(term.term, self) };

        result != 0
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
        assert!(term1.unify(42_u64));
        assert!(term2.unify(42_u64));
        assert!(term1.unify(&term2));
    }

    #[test]
    fn unify_some_terms_with_failure() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = context.new_term_ref();
        let term2 = context.new_term_ref();
        assert!(term1.unify(42_u64));
        assert!(term2.unify(43_u64));
        assert!(!term1.unify(&term2));
    }

    #[test]
    fn unify_twice_different_failure() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.new_term_ref();
        assert!(term.unify(42_u64));
        assert!(!term.unify(43_u64));
    }

    #[test]
    fn unify_twice_different_with_rewind_success() {
        initialize_swipl_noengine();
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();
        let term = context.new_term_ref();
        let context2 = context.open_frame();

        assert!(term.unify(42_u64));
        context2.rewind_frame();
        assert!(term.unify(43_u64));
    }
}
