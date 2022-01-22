use std::collections::HashMap;
use super::prelude::*;
use super::fli;

#[derive(PartialEq, Eq, Hash)]
pub enum Key {
    Int(u64),
    Atom(Atom)
}

impl From<u64> for Key {
    fn from(val: u64) -> Self {
        Self::Int(val)
    }
}

impl<A:IntoAtom> From<A> for Key {
    fn from(val: A) -> Self {
        Self::Atom(val.into_atom())
    }
}

const INT_SHIFT:u8 = (std::mem::size_of::<fli::atom_t>() * 8 - 7) as u8;

fn int_to_atom_t(val: u64) -> fli::atom_t {
    if (val >> INT_SHIFT) != 0 {
        panic!("val {} is too large to be converted to an atom_t", val);
    }

    (val << 7 | 0x3) as fli::atom_t
}

impl Key {
    fn atom_ptr(&self) -> fli::atom_t {
        match self {
            Key::Int(i) => int_to_atom_t(*i),
            Key::Atom(a) => a.atom_ptr()
        }
    }
}

pub trait AsKey {
    fn atom_ptr(&self) -> (fli::atom_t, Option<Atom>);
}

impl<A:AsAtom> AsKey for A {
    fn atom_ptr(&self) -> (fli::atom_t, Option<Atom>) {
        self.as_atom_ptr()
    }
}

impl AsKey for u64 {
    fn atom_ptr(&self) -> (fli::atom_t, Option<Atom>) {
        (int_to_atom_t(*self), None)
    }
}

pub struct DictBuilder<'a> {
    tag: Option<Atom>,
    entries: HashMap<Key, Option<Box<dyn TermPutable+'a>>>
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

    pub fn add_entry_key<K:Into<Key>>(&mut self, key: K) {
        self.entries.insert(key.into(), None);
    }

    pub fn entry_key<K:Into<Key>>(mut self, key: K) -> Self {
        self.add_entry_key(key);

        self
    }

    pub fn add_entry<K:Into<Key>,P:TermPutable+'a>(&mut self, key: K, val: P) {
        self.entries.insert(key.into(), Some(Box::new(val)));
    }

    pub fn entry<K:Into<Key>,P:TermPutable+'a>(mut self, key: K, val: P) -> Self {
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

unsafe impl<'a> Unifiable for DictBuilder<'a> {
    fn unify(&self, term: &Term) -> bool {
        term.assert_term_handling_possible();
        let context = unsafe { unmanaged_engine_context() };

        let dict_term = context.new_term_ref();
        self.put(&dict_term);

        let result = unsafe { fli::PL_unify(dict_term.term_ptr(), term.term_ptr()) != 0 };
        unsafe { dict_term.reset(); };

        result
    }
}

impl<'a> Term<'a> {
    pub fn get_dict_key<K:AsKey>(&self, key: K, term: &Term) -> PrologResult<()> {
        let (key_atom, alloc) = key.atom_ptr();

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

        let string_term = context.new_term_ref();
        context.call_once(pred!{term_string/2}, [&dict_term, &string_term]).unwrap();
        let string = string_term.get::<String>().unwrap();
        assert_eq!("foo{a:42,b:10}", string);
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

    #[test]
    fn construct_dict_with_smallints() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let dict = DictBuilder::new()
            .tag("foo")
            .entry(42, atomable("foo"))
            .entry(11, atomable("bar"));

        let dict_term = context.new_term_ref();
        let [val1, val2, val3] = context.new_term_refs();
        dict_term.put(&dict).unwrap();

        assert!(attempt(dict_term.get_dict_key(11, &val1)).unwrap());
        assert!(attempt(dict_term.get_dict_key(42, &val2)).unwrap());
        assert!(!attempt(dict_term.get_dict_key(50, &val3)).unwrap());

        assert_eq!(Atom::new("bar"), val1.get().unwrap());
        assert_eq!(Atom::new("foo"), val2.get().unwrap());

        let string_term = context.new_term_ref();
        context.call_once(pred!{term_string/2}, [&dict_term, &string_term]).unwrap();
        let string = string_term.get::<String>().unwrap();
        assert_eq!("foo{11:bar,42:foo}", string);
    }

    #[test]
    fn unify_dicts() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let [dict1, dict2, dict3] = context.new_term_refs();

        let dict1_builder = DictBuilder::new()
            .tag("foo")
            .entry("a", 42_u64)
            .entry("b", 10_u64);
        let dict2_builder = DictBuilder::new()
            .tag("foo")
            .entry("a", 42_u64)
            .entry("c", 11_u64);

        dict1.put(&dict1_builder).unwrap();
        dict2.put(&dict1_builder).unwrap();
        dict3.put(&dict2_builder).unwrap();

        assert!(attempt(dict1.unify(&dict2)).unwrap());
        assert!(!attempt(dict1.unify(&dict3)).unwrap());
    }
}
