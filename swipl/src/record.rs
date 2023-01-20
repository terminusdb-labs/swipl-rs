//! Records - prolog terms in heap storage.
//!
//! SWI-Prolog allows the storing of terms into records, which are
//! opaque handles which remain valid until they are explicitely
//! erased. This module wraps such records, making the erase happen
//! automatically on drop of a wrapper object.

use super::fli;
use super::result::*;
use super::term::*;
use crate::{term_getable, term_putable, unifiable};

/// A recorded term.
///
/// Recorded terms live off the stack, and remain valid until
/// explicitely dropped. They can be used to copy terms to other
/// threads, or to keep a template of a term around for repeated use.
pub struct Record {
    record: fli::record_t,
}

impl Record {
    /// Extract a record from the given term.
    pub fn from_term(term: &Term) -> Record {
        term.assert_term_handling_possible();
        unsafe {
            let record = fli::PL_record(term.term_ptr());

            Record { record }
        }
    }

    /// Copy the recorded term into the given term reference.
    pub fn recorded(&self, term: &Term) -> PrologResult<()> {
        term.assert_term_handling_possible();
        unsafe { into_prolog_result(fli::PL_recorded(self.record, term.term_ptr()) != 0) }
    }
}

impl Clone for Record {
    fn clone(&self) -> Self {
        unsafe {
            let new_record = fli::PL_duplicate_record(self.record);
            assert!(self.record == new_record);

            Record { record: new_record }
        }
    }
}

impl Drop for Record {
    fn drop(&mut self) {
        unsafe {
            fli::PL_erase(self.record);
        }
    }
}

term_putable! {
    (self: Record, term) => {
        self.recorded(term).expect("expected record to be putable");
    }
}

term_getable! {
    (Record, term) => {
        Some(Record::from_term(term))
    }
}

unifiable! {
    (self:Record, term) => {
        // we need an extra term for this, so we have to be very careful about clearing it up before we're out of here.
        unsafe {
            let extra_term = fli::PL_new_term_ref();
            fli::PL_recorded(self.record, extra_term);
            let result = fli::PL_unify(term.term_ptr(), extra_term);
            fli::PL_reset_term_refs(extra_term);

            result != 0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::*;
    use crate::engine::*;
    use crate::term;

    #[test]
    fn record_and_put() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = term! {context: foo(bar(baz, quux))}.unwrap();

        let record = term1.record();

        let term2 = context.new_term_ref();
        term2.put(&record).unwrap();

        assert!(term1 == term2);
    }

    #[test]
    fn record_and_put_var() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = term! {context: foo(bar(baz, _))}.unwrap();

        let record = term1.record();

        let term2 = context.new_term_ref();
        term2.put(&record).unwrap();

        // these two terms are not equal, as the variables should be different
        assert!(term1 != term2);
        // but they should still be unifiable
        term1.unify(term2).unwrap();
    }

    #[test]
    fn record_get_and_put() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = term! {context: foo(bar(baz, quux))}.unwrap();

        let record: Record = term1.get().unwrap();

        let term2 = context.new_term_ref();
        term2.put(&record).unwrap();

        assert!(term1 == term2);
    }

    #[test]
    fn record_and_put_on_other_engine() {
        let record: Record;
        {
            let engine = Engine::new();
            let activation = engine.activate();
            let context: Context<_> = activation.into();

            let term = term! {context: foo(bar(baz, quux))}.unwrap();
            record = term.record();
        }

        // engine has entirely been dropped at this point.
        // but we should still have the same term in our record!
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = term! {context: foo(bar(baz, quux))}.unwrap();
        let term2 = context.new_term_ref();
        term2.put(&record).unwrap();

        assert!(term1 == term2);
    }

    #[test]
    fn record_clone_drop_put() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = term! {context: foo(bar(baz, quux))}.unwrap();
        let record1 = term1.record();

        let record2 = record1.clone();
        let record3 = record2.clone();

        std::mem::drop(record1);
        std::mem::drop(record2);

        let term2 = context.new_term_ref();
        term2.put(&record3).unwrap();

        assert!(term1 == term2);
    }

    #[test]
    fn record_unify_self() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = term! {context: foo(bar(baz, quux))}.unwrap();
        let record = term.record();

        term.unify(&record).unwrap();
    }

    #[test]
    fn record_unify_var() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = term! {context: foo(bar(baz, quux))}.unwrap();
        let record = term1.record();
        let term2 = context.new_term_ref();

        term2.unify(&record).unwrap();
    }

    #[test]
    fn record_unify_dif_fails() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term1 = term! {context: foo(bar(baz, quux))}.unwrap();
        let record = term1.record();
        let term2 = term! {context: something(completely(different))}.unwrap();

        assert!(!attempt(term2.unify(&record)).unwrap());
    }
}
