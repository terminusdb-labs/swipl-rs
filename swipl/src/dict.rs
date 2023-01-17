//! Prolog dictionaries.
//!
//! SWI-Prolog has a very convenient dictionary implementation. This
//! module allows one to create dictionaries, as well as extract them.
use super::fli;
use super::prelude::*;
use std::collections::HashMap;

/// A key in a prolog dictionary.
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Key {
    Int(u64),
    Atom(Atom),
}

enum DictTag<'a> {
    Atom(Atom),
    Term(Term<'a>),
    Var,
}

impl From<u64> for Key {
    fn from(val: u64) -> Self {
        Self::Int(val)
    }
}

impl<A: IntoAtom> From<A> for Key {
    fn from(val: A) -> Self {
        Self::Atom(val.into_atom())
    }
}

const INT_SHIFT: u8 = (std::mem::size_of::<fli::atom_t>() * 8 - 7) as u8;

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
            Key::Atom(a) => a.atom_ptr(),
        }
    }
}

/// Trait for things that can behave as a key for the purpose of
/// retrieving values from a prolog dictionary.
///
/// A prolog dictionary key can either be an atom or an integer. In
/// addition, various things can be automatically converted to
/// atoms. This trait provides an implementation which facilitates
/// this.
pub trait IntoKey {
    /// Returns the `atom_t` corresponding to this key, plus an allocation.
    ///
    /// As long as the allocation remains in scope, the atom_t can be
    /// considered safe to use in unsafe code.
    ///
    /// This is used by dict querying code to efficiently get hold of
    /// dictionary keys (which internally are always atom_t).
    fn atom_ptr(self) -> (fli::atom_t, Option<Atom>);
}

impl<'a, A: AsAtom + ?Sized> IntoKey for &'a A {
    fn atom_ptr(self) -> (fli::atom_t, Option<Atom>) {
        self.as_atom_ptr()
    }
}

impl IntoKey for u64 {
    fn atom_ptr(self) -> (fli::atom_t, Option<Atom>) {
        (int_to_atom_t(self), None)
    }
}

/// A builder for prolog dictionaries.
///
/// A dictionary can be constructed by first using the various builder
/// functions on this type, and then either putting or unifying the
/// builder with a term.
///
/// Example:
/// ```
/// # use swipl::prelude::*;
/// fn build_example_dict(term: &Term) -> PrologResult<()> {
///     let dict = DictBuilder::new()
///         .tag("some_tag")
///         .entry("foo", 42_u64)
///         .entry("bar", "hello".to_owned());
///
///     term.put(&dict)?;
///     Ok(())
/// }
/// ```
///
/// This will create a prolog dictionary which looks like this:
/// ```prolog
/// some_tag{
///     foo: 42,
///     bar: "hello"
/// }
/// ```

pub struct DictBuilder<'a> {
    tag: DictTag<'a>,
    entries: HashMap<Key, Option<Box<dyn TermPutable + 'a>>>,
}

impl<'a> DictBuilder<'a> {
    /// Create a new dictionary builder.
    pub fn new() -> Self {
        Self {
            tag: DictTag::Var,
            entries: HashMap::new(),
        }
    }

    /// Set the dictionary tag to the given atom.
    pub fn set_tag<A: IntoAtom>(&mut self, tag: A) {
        self.tag = DictTag::Atom(tag.into_atom());
    }

    /// Set the dictionary tag to the given atom.
    pub fn tag<A: IntoAtom>(mut self, tag: A) -> Self {
        self.set_tag(tag);

        self
    }

    /// Set the dictionary tag to the given term.
    pub fn set_tag_term(&mut self, term: Term<'a>) {
        self.tag = DictTag::Term(term);
    }

    /// Set the dictionary tag to the given term.
    pub fn tag_term(mut self, term: Term<'a>) -> Self {
        self.set_tag_term(term);

        self
    }

    /// add an entry with the given key to the dictionary. The value
    /// is implied to be a variable.
    ///
    /// If the entry already exists, this will overwrite it.
    ///
    /// The key can either be an atom (or something that can be turned
    /// into an atom), or an integer.
    pub fn add_entry_key<K: Into<Key>>(&mut self, key: K) {
        self.entries.insert(key.into(), None);
    }

    /// add an entry with the given key to the dictionary. The value
    /// is implied to be a variable.
    ///
    /// If the entry already exists, this will overwrite it.
    ///
    /// The key can either be an atom (or something that can be turned
    /// into an atom), or an integer.
    pub fn entry_key<K: Into<Key>>(mut self, key: K) -> Self {
        self.add_entry_key(key);

        self
    }

    /// Add an entry with the given key and value to the dictionary.
    ///
    /// If the entry already exists, this will overwrite it.
    ///
    /// The key can either be an atom (or something that can be turned
    /// into an atom), or an integer.
    pub fn add_entry<K: Into<Key>, P: TermPutable + 'a>(&mut self, key: K, val: P) {
        self.entries.insert(key.into(), Some(Box::new(val)));
    }

    /// Add an entry with the given key and value to the dictionary.
    ///
    /// If the entry already exists, this will overwrite it.
    ///
    /// The key can either be an atom (or something that can be turned
    /// into an atom), or an integer.
    pub fn entry<K: Into<Key>, P: TermPutable + 'a>(mut self, key: K, val: P) -> Self {
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
                term.put(&**value)
                    .expect("term put errored while building dict");
                value_term += 1;
            }
        }

        match &self.tag {
            DictTag::Atom(t) => t.put(&tag_term),
            DictTag::Var => {}
            DictTag::Term(t) => TermPutable::put(t, &tag_term),
        };

        unsafe {
            fli::PL_put_dict(
                term.term_ptr(),
                0,
                len as fli::size_t,
                key_atoms.as_ptr(),
                value_terms,
            );

            fli::PL_unify_arg(1, term.term_ptr(), tag_term.term_ptr());

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
        unsafe {
            dict_term.reset();
        };

        result
    }
}

impl<'a> Term<'a> {
    /// Get the value of the given key in the dictionary contained in
    /// the dictionary contained in this term.
    ///
    /// If the dictionary doesn't contain the key, or if the expected
    /// type is different, this will fail. If the given term doesn't
    /// contain a dictionary, this will always fail. Otherwise, the
    /// value corresponding to the given key is returned.
    pub fn get_dict_key<K: IntoKey, G: TermGetable>(&self, key: K) -> PrologResult<G> {
        self.assert_term_handling_possible();
        let context = unsafe { unmanaged_engine_context() };
        let (key_atom, alloc) = key.atom_ptr();
        let term = context.new_term_ref();

        let get_result =
            unsafe { fli::PL_get_dict_key(key_atom, self.term_ptr(), term.term_ptr()) != 0 };
        std::mem::drop(alloc); // purely to get rid of the never-read warning

        let result = if unsafe { fli::pl_default_exception() != 0 } {
            Err(PrologError::Exception)
        } else if get_result {
            term.get()
        } else {
            Err(PrologError::Failure)
        };

        unsafe {
            term.reset();
        }

        result
    }

    /// Get the value of the given key in the dictionary contained in
    /// the dictionary contained in this term.
    ///
    /// If the dictionary doesn't contain the key, this will fail. If
    /// the given term doesn't contain a dictionary, this will always
    /// fail. Otherwise, the term argument will be overwritten with
    /// the value corresponding to the key.
    pub fn get_dict_key_term<K: IntoKey>(&self, key: K, term: &Term) -> PrologResult<()> {
        self.assert_term_handling_possible();
        if self.origin_engine_ptr() != term.origin_engine_ptr() {
            panic!("terms being unified are not part of the same engine");
        }
        let (key_atom, alloc) = key.atom_ptr();

        let result =
            unsafe { fli::PL_get_dict_key(key_atom, self.term_ptr(), term.term_ptr()) != 0 };
        std::mem::drop(alloc); // purely to get rid of the never-read warning

        if unsafe { fli::pl_default_exception() != 0 } {
            Err(PrologError::Exception)
        } else if result {
            Ok(())
        } else {
            Err(PrologError::Failure)
        }
    }

    /// Get the tag of this dictionary.
    ///
    /// Tag is assumed to be an atom. If it isn't (because it is
    /// either a variable or some other kind of term), None will be
    /// returned. Otherwise Some(atom) will be returned.
    ///
    /// If this is not a dictionary, this method will fail.
    ///
    /// If tag could be a non-atom term, consider using
    /// [get_dict_tag_term](Term::get_dict_tag_term) instead.
    pub fn get_dict_tag(&self) -> PrologResult<Option<Atom>> {
        self.assert_term_handling_possible();

        if unsafe { fli::PL_is_dict(self.term_ptr()) == 0 } {
            Err(PrologError::Failure)
        } else if let Some(atom) = attempt_opt(self.get_arg(1))? {
            Ok(Some(atom))
        } else {
            Ok(None)
        }
    }

    /// Get the tag of this dictionary and put it in the given term.
    ///
    /// Unlike [get_dict_tag](Term::get_dict_tag), this is able to
    /// extract complex dictionary tags. Though uncommon, a dictionary
    /// tag can actually be any valid prolog term. This method helps
    /// in extracting that.
    ///
    /// If this is not a dictionary, this method will fail.
    pub fn get_dict_tag_term(&self, term: &Term) -> PrologResult<()> {
        self.assert_term_handling_possible();
        if self.origin_engine_ptr() != term.origin_engine_ptr() {
            panic!("terms being unified are not part of the same engine");
        }

        if unsafe { fli::PL_is_dict(self.term_ptr()) == 0 } {
            Err(PrologError::Failure)
        } else {
            self.unify_arg(1, term)
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
                let functor: Functor = term
                    .get()
                    .expect("Expected to be able to get a functor out of a dict term");
                Some((functor.arity() as usize - 1) / 2)
            }
        };

        DictIterator {
            context: self,
            term: term.clone(),
            count,
            index: 0,
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

impl<'a, 'b, T: QueryableContextType> Iterator for DictIterator<'a, 'b, T> {
    type Item = (Key, Term<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        match self.count {
            None => None,
            Some(count) => {
                if self.index < count {
                    let [val_term, key_term] = self.context.new_term_refs();
                    self.term
                        .unify_arg(self.index * 2 + 2, &val_term)
                        .expect("unify dict val arg failed");
                    self.term
                        .unify_arg(self.index * 2 + 3, &key_term)
                        .expect("unify dict val arg failed");

                    let key;
                    if key_term.is_atom() {
                        key = Key::Atom(key_term.get().unwrap());
                    } else if key_term.is_integer() {
                        key = Key::Int(key_term.get().unwrap());
                    } else {
                        panic!("Encountered term key that was neither an atom nor an integer");
                    }

                    // we don't need the key term after this, so no
                    // point in letting it hang around on the stack.
                    unsafe {
                        key_term.reset();
                    }

                    self.index += 1;

                    Some((key, val_term))
                } else {
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

        assert!(attempt(dict_term.get_dict_key_term("a", &val1)).unwrap());
        assert!(attempt(dict_term.get_dict_key_term("b", &val2)).unwrap());
        assert!(!attempt(dict_term.get_dict_key_term("c", &val3)).unwrap());

        assert_eq!(42, val1.get::<u64>().unwrap());
        assert_eq!(10, val2.get::<u64>().unwrap());

        let string_term = context.new_term_ref();
        context
            .call_once(pred! {term_string/2}, [&dict_term, &string_term])
            .unwrap();
        let string = string_term.get::<String>().unwrap();
        assert_eq!("foo{a:42,b:10}", string);
    }

    #[test]
    fn get_dict_key_term_for_nondict() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let nondict = context.new_term_ref();
        nondict.put_val(42_u64).unwrap();

        let query = context.new_term_ref();

        let result = nondict.get_dict_key_term("a", &query).unwrap_err();
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

        assert!(attempt(dict_term.get_dict_key_term(11, &val1)).unwrap());
        assert!(attempt(dict_term.get_dict_key_term(42, &val2)).unwrap());
        assert!(!attempt(dict_term.get_dict_key_term(50, &val3)).unwrap());

        assert_eq!(Atom::new("bar"), val1.get().unwrap());
        assert_eq!(Atom::new("foo"), val2.get().unwrap());

        let string_term = context.new_term_ref();
        context
            .call_once(pred! {term_string/2}, [&dict_term, &string_term])
            .unwrap();
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

    #[test]
    fn get_dict_tag_var() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let builder = DictBuilder::new();

        let term = context.new_term_ref();
        term.unify(&builder).unwrap();

        assert!(term.get_dict_tag().unwrap().is_none());
    }

    #[test]
    fn get_dict_tag_atom() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let builder = DictBuilder::new().tag("foo");

        let term = context.new_term_ref();
        term.unify(&builder).unwrap();

        assert_eq!(Some(Atom::new("foo")), term.get_dict_tag().unwrap());
    }

    #[test]
    fn get_nondict_tag() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.new_term_ref();
        term.unify(42_u64).unwrap();

        assert!(term.get_dict_tag().unwrap_err().is_failure());
    }

    #[test]
    fn get_dict_tag_term() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let [dict, tag, tag2] = context.new_term_refs();
        tag.unify(42_u64).unwrap();
        let builder = DictBuilder::new().tag_term(tag.clone());

        dict.unify(&builder).unwrap();

        dict.get_dict_tag_term(&tag2).unwrap();
        assert_eq!(42_u64, tag2.get::<u64>().unwrap());
        tag.unify(&tag2).unwrap();
    }

    #[test]
    fn get_dict_key() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let dict = context.new_term_ref();
        let builder = DictBuilder::new()
            .entry("foo", 42_u64)
            .entry("bar", "hello".to_owned());

        dict.unify(&builder).unwrap();

        assert_eq!(42_u64, dict.get_dict_key::<_, u64>("foo").unwrap());
        let hello_str: String = dict.get_dict_key("bar").unwrap();
        assert_eq!("hello", hello_str);

        // getting a dict key for the wrong type fails
        assert!(attempt_opt(dict.get_dict_key::<_, String>("foo"))
            .unwrap()
            .is_none());
        // getting a dict key that is not in there fails
        assert!(attempt_opt(dict.get_dict_key::<_, bool>("moo"))
            .unwrap()
            .is_none());
    }

    #[test]
    fn get_dict_key_for_nondict() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let nondict = context.new_term_ref();
        nondict.put_val(42_u64).unwrap();

        let result = nondict.get_dict_key::<_, String>("a").unwrap_err();

        assert!(result.is_failure());
    }
}
