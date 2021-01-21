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

    pub fn unify<U: Unifiable>(&self, unifiable: U) -> bool {
        if !self.context.is_engine_active() {
            panic!("term is not part of an active engine");
        }

        // unsafe justification: we ensured that the correct engine is active above
        unifiable.unify(self)
    }
}

pub trait TermOrigin {
    fn origin_engine_ptr(&self) -> PL_engine_t;
    fn is_engine_active(&self) -> bool;
}

pub trait Unifiable {
    fn unify(self, term: &Term) -> bool;
}

impl<'a> Unifiable for &Term<'a> {
    fn unify(self, other: &Term) -> bool {
        if self.context.origin_engine_ptr() != other.context.origin_engine_ptr() {
            panic!("terms being unified are not part of the same engine");
        }

        // unsafe justification: the fact that we have terms here means we are dealing with some kind of active context, and therefore an initialized swipl. The checks above have made sure that both terms are part of the same engine too, and that this engine is the current engine.
        let result = unsafe { PL_unify(self.term, other.term) };

        // TODO we should actually properly test for an exception here.
        result != 0
    }
}

impl Unifiable for bool {
    fn unify(self, term: &Term) -> bool {
        let num = match self {
            true => 0,
            false => 1,
        };
        let result = unsafe { PL_unify_bool(term.term, num) };

        result != 0
    }
}

impl Unifiable for u64 {
    fn unify(self, term: &Term) -> bool {
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
