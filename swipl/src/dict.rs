use std::collections::HashMap;
use super::prelude::*;
use super::fli;

pub struct DictBuilder<'a> {
    tag: Option<Atom>,
    entries: HashMap<Atom, Option<Box<dyn TermPutable+'a>>>
}

impl<'a> DictBuilder<'a> {
    pub fn new() -> Self {
        Self {
            tag: None,
            entries: HashMap::new()
        }
    }

    pub fn set_tag<A:IntoAtom>(&mut self, tag: A) {
        self.tag = Some(tag.into_atom());
    }

    pub fn tag<A:IntoAtom>(mut self, tag: A) -> Self {
        self.set_tag(tag);

        self
    }

    pub fn add_entry_key<A:IntoAtom>(&mut self, key: A) {
        self.entries.insert(key.into_atom(), None);
    }

    pub fn entry_key<A:IntoAtom>(mut self, key: A) -> Self {
        self.add_entry_key(key);

        self
    }

    pub fn add_entry<A:IntoAtom,P:TermPutable+'a>(&mut self, key: A, val: P) {
        self.entries.insert(key.into_atom(), Some(Box::new(val)));
    }

    pub fn entry<A:IntoAtom,P:TermPutable+'a>(mut self, key: A, val: P) -> Self {
        self.add_entry(key, val);

        self
    }
}

unsafe impl<'a> TermPutable for DictBuilder<'a> {
    fn put(&self, term: &Term) {
        term.assert_term_handling_possible();
        let context = unsafe { unmanaged_engine_context() };

        let tag_term = context.new_term_ref();
        let len = self.entries.len();
        // TODO assert len is not too big
        let value_terms = unsafe { fli::PL_new_term_refs(len as i32) };
        let mut value_term = value_terms;
        let mut key_atoms = Vec::with_capacity(len);

        for (key, value) in self.entries.iter() {
            key_atoms.push(key.atom_ptr());
            if let Some(value) = value {
                let term = unsafe { Term::new(value_term, context.as_term_origin()) };
                term.put(&**value).expect("term put errored while building dict");
                value_term += 1;
            }
        }

        let tag = match &self.tag {
            Some(t) => t.atom_ptr(),
            None => 0
        };

        unsafe {
            fli::PL_put_dict(term.term_ptr(), tag, len as fli::size_t, key_atoms.as_ptr(), value_terms);

            tag_term.reset();
        }
    }
}

impl<'a> Term<'a> {
    pub fn get_dict_key<A:AsAtom>(&self, key: A, term: &Term) -> PrologResult<()> {
        let (key_atom, alloc) = key.as_atom_ptr();

        let result = unsafe { fli::PL_get_dict_key(key_atom, self.term_ptr(), term.term_ptr()) != 0 };
        std::mem::drop(alloc); // purely to get rid of the never-read warning

        if unsafe { fli::pl_default_exception() != 0 } {
            Err(PrologError::Exception)
        } else if result {
            Ok(())
        } else {
            Err(PrologError::Failure)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn construct_dict() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let dict = DictBuilder::new()
            .tag("foo")
            .entry("a", 42_u64)
            .entry("b", 10_u64);

        let dict_term = context.new_term_ref();
        let [val1, val2, val3] = context.new_term_refs();
        dict_term.put(&dict).unwrap();

        assert!(attempt(dict_term.get_dict_key("a", &val1)).unwrap());
        assert!(attempt(dict_term.get_dict_key("b", &val2)).unwrap());
        assert!(!attempt(dict_term.get_dict_key("c", &val3)).unwrap());

        assert_eq!(42, val1.get::<u64>().unwrap());
        assert_eq!(10, val2.get::<u64>().unwrap());

        context.call_once(pred!{writeq/1}, [&dict_term]).unwrap();
        context.call_once(pred!{nl/0}, []).unwrap();
    }

    #[test]
    fn get_dict_key_for_nondict() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let nondict = context.new_term_ref();
        nondict.put_val(42_u64).unwrap();

        let query = context.new_term_ref();

        let result = nondict.get_dict_key("a", &query).unwrap_err();
        // TODO - documentation says this should actually be an
        // exception but this does not appear to be happening.
        assert!(result.is_failure());
    }
}
