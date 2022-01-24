use std::collections::HashMap;
use super::prelude::*;
use super::fli;

#[derive(PartialEq, Eq, Hash, Debug)]
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

    /// Returns true if this term reference holds a dictionary.
    pub fn is_dict(&self) -> bool {
        self.assert_term_handling_possible();
        unsafe { fli::PL_is_dict(self.term_ptr()) != 0 }
    }
}

impl<'a, T: QueryableContextType> Context<'a, T> {
    /// Iterate over the entries in the dictionary referred to by this term.
    ///
    /// This will return key-value pairs, where the key is either an
    /// atom or an integer, and the value is a term. The term will be
    /// created in the current context. A consequence of this is that
    /// the iterator will panic if this context is not active.
    ///
    /// Created terms will not be automatically unallocated when the
    /// iterator moves on. It is the responsibility of the caller to
    /// clear them if desired using either a frame or by resetting.
    ///
    /// If `dict_entries` is called on a term that does not contain a
    /// dictionary, the iterator is still created but will not return
    /// any elements.
    pub fn dict_entries<'b>(&'b self, term: &Term<'b>) -> DictIterator<'a, 'b, T> {
        self.assert_activated();
        let count = match term.is_dict() {
            false => None,
            true => {
                let functor: Functor = term.get().expect("Expected to be able to get a functor out of a dict term");
                Some((functor.arity() as usize -1)/2)
            }
        };

        DictIterator {
            context: self,
            term: term.clone(),
            count,
            index: 0
        }
    }
}

/// An iterator over the entries of a dict term.
///
/// See [dict_entries](Context::dict_entries) for more information.
pub struct DictIterator<'a, 'b, T: QueryableContextType> {
    context: &'a Context<'b, T>,
    term: Term<'a>,
    count: Option<usize>,
    index: usize,
}

impl<'a, 'b, T:QueryableContextType> Iterator for DictIterator<'a, 'b, T> {
    type Item = (Key, Term<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        match self.count {
            None => None,
            Some(count) => {
                if self.index < count {
                    let [val_term, key_term] = self.context.new_term_refs();
                    self.term.unify_arg(self.index*2+2, &val_term).expect("unify dict val arg failed");
                    self.term.unify_arg(self.index*2+3, &key_term).expect("unify dict val arg failed");

                    let key;
                    if key_term.is_atom() {
                        key = Key::Atom(key_term.get().unwrap());
                    }
                    else if key_term.is_integer() {
                        key = Key::Int(key_term.get().unwrap());
                    }
                    else {
                        panic!("Encountered term key that was neither an atom nor an integer");
                    }

                    // we don't need the key term after this, so no
                    // point in letting it hang around on the stack.
                    unsafe {
                        key_term.reset();
                    }

                    self.index += 1;

                    Some((key, val_term))
                }
                else {
                    None
                }
            }
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

    #[test]
    fn iterate_dict() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let builder = DictBuilder::new()
            .entry(8, atomable("foo"))
            .entry(2, atomable("bar"))
            .entry(7, atomable("baz"))
            .entry(11, atomable("quux"));

        let term = context.new_term_ref();
        term.unify(&builder).unwrap();

        let mut iter = context.dict_entries(&term);
        let (key1, val1) = iter.next().unwrap();
        let (key2, val2) = iter.next().unwrap();
        let (key3, val3) = iter.next().unwrap();
        let (key4, val4) = iter.next().unwrap();

        assert!(iter.next().is_none());

        assert_eq!(Key::Int(2), key1);
        assert_eq!(Key::Int(7), key2);
        assert_eq!(Key::Int(8), key3);
        assert_eq!(Key::Int(11), key4);

        assert_eq!(Atom::new("bar"), val1.get().unwrap());
        assert_eq!(Atom::new("baz"), val2.get().unwrap());
        assert_eq!(Atom::new("foo"), val3.get().unwrap());
        assert_eq!(Atom::new("quux"), val4.get().unwrap());
    }

    #[test]
    fn iterate_nondict_as_dict() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.new_term_ref();
        term.unify(42_u64).unwrap();

        let mut iter = context.dict_entries(&term);
        assert!(iter.next().is_none());
    }
}
