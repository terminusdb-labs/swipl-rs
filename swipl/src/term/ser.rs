use super::de::Error;
use super::*;
use crate::dict::{DictBuilder, Key};
use crate::functor::Functor;
use crate::{atom, functor};
use serde::ser::Impossible;
use serde::{self, ser, Serialize};

pub(crate) const ATOM_STRUCT_NAME: &'static str = "$swipl::private::atom";

impl ser::Error for Error {
    fn custom<T>(c: T) -> Self
    where
        T: std::fmt::Display,
    {
        Self::Message(c.to_string())
    }
}

pub fn to_term<'a, T, C: QueryableContextType>(
    context: &'a Context<C>,
    obj: &T,
    term: &Term<'a>,
) -> Result<(), Error>
where
    T: Serialize,
{
    let serializer = Serializer {
        context,
        term: term.clone(),
    };

    obj.serialize(serializer)
}

fn attempt_unify<U: Unifiable>(term: &Term, v: U) -> Result<(), Error> {
    if attempt(term.unify(v))? {
        Ok(())
    } else {
        Err(Error::UnificationFailed)
    }
}

pub struct Serializer<'a, C: QueryableContextType> {
    context: &'a Context<'a, C>,
    term: Term<'a>,
}

impl<'a, C: QueryableContextType> serde::Serializer for Serializer<'a, C> {
    type Ok = ();
    type Error = Error;
    type SerializeSeq = SerializeSeq<'a, C>;
    type SerializeTuple = SerializeTuple<'a, C>;
    type SerializeTupleStruct = SerializeNamedTuple<'a, C>;
    type SerializeTupleVariant = SerializeNamedTuple<'a, C>;
    type SerializeMap = SerializeMap<'a, C>;
    type SerializeStruct = SerializeMap<'a, C>;
    type SerializeStructVariant = SerializeMap<'a, C>;

    fn serialize_bool(self, v: bool) -> Result<Self::Ok, Self::Error> {
        attempt_unify(&self.term, v)
    }
    fn serialize_i8(self, v: i8) -> Result<Self::Ok, Self::Error> {
        self.serialize_i64(v as i64)
    }
    fn serialize_i16(self, v: i16) -> Result<Self::Ok, Self::Error> {
        self.serialize_i64(v as i64)
    }
    fn serialize_i32(self, v: i32) -> Result<Self::Ok, Self::Error> {
        self.serialize_i64(v as i64)
    }
    fn serialize_i64(self, v: i64) -> Result<Self::Ok, Self::Error> {
        attempt_unify(&self.term, v)
    }
    fn serialize_u8(self, v: u8) -> Result<Self::Ok, Self::Error> {
        self.serialize_u64(v as u64)
    }
    fn serialize_u16(self, v: u16) -> Result<Self::Ok, Self::Error> {
        self.serialize_u64(v as u64)
    }
    fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error> {
        self.serialize_u64(v as u64)
    }
    fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error> {
        attempt_unify(&self.term, v)
    }
    fn serialize_f32(self, v: f32) -> Result<Self::Ok, Self::Error> {
        self.serialize_f64(v as f64)
    }
    fn serialize_f64(self, v: f64) -> Result<Self::Ok, Self::Error> {
        attempt_unify(&self.term, v)
    }
    fn serialize_char(self, v: char) -> Result<Self::Ok, Self::Error> {
        attempt_unify(&self.term, Atomable::String(v.to_string()))
    }
    fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
        attempt_unify(&self.term, v)
    }
    fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error> {
        attempt_unify(&self.term, v)
    }
    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        attempt_unify(&self.term, atom!("none"))
    }
    fn serialize_some<T: ?Sized>(self, value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize,
    {
        if attempt(self.term.unify(functor!("some/1")))? {
            let [term] = attempt_opt(self.context.compound_terms(&self.term))?.expect("having just unified the functor some/1, retrieving its argument list should have been possible");
            let inner_serializer = Serializer {
                context: self.context,
                term: term.clone(),
            };
            let result = value.serialize(inner_serializer);
            unsafe {
                term.reset();
            }
            result
        } else {
            Err(Error::UnificationFailed)
        }
    }
    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        attempt_unify(&self.term, Nil)
    }
    fn serialize_unit_struct(self, name: &'static str) -> Result<Self::Ok, Self::Error> {
        attempt_unify(&self.term, Atom::new(name))
    }
    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        attempt_unify(&self.term, Atom::new(variant))
    }
    fn serialize_newtype_struct<T: ?Sized>(
        self,
        name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize,
    {
        if name == ATOM_STRUCT_NAME {
            value.serialize(AtomEmitter(self.term))
        } else {
            if attempt(self.term.unify(Functor::new(name, 1)))? {
                let [term] = attempt_opt(self.context.compound_terms(&self.term))?.expect("having just unified the functor with arity 1, retrieving its argument list should have been possible");
                let inner_serializer = Serializer {
                    context: self.context,
                    term: term.clone(),
                };
                let result = value.serialize(inner_serializer);
                unsafe {
                    term.reset();
                }
                result
            } else {
                Err(Error::UnificationFailed)
            }
        }
    }
    fn serialize_newtype_variant<T: ?Sized>(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize,
    {
        if attempt(self.term.unify(Functor::new(variant, 1)))? {
            let [term] = attempt_opt(self.context.compound_terms(&self.term))?.expect("having just unified the functor with arity 1, retrieving its argument list should have been possible");
            let inner_serializer = Serializer {
                context: self.context,
                term: term.clone(),
            };
            let result = value.serialize(inner_serializer);
            unsafe {
                term.reset();
            }
            result
        } else {
            Err(Error::UnificationFailed)
        }
    }
    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Ok(SerializeSeq {
            context: self.context,
            term: self.term.clone(),
        })
    }
    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        Ok(SerializeTuple {
            context: self.context,
            term: self.term.clone(),
            len,
        })
    }
    fn serialize_tuple_struct(
        self,
        name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        if len > u16::MAX as usize {
            return Err(Error::UnsupportedValue);
        }

        attempt_unify(&self.term, Functor::new(name, len as u16))?;

        Ok(SerializeNamedTuple {
            context: self.context,
            term: self.term.clone(),
            pos: 0,
        })
    }
    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        // we serialize based on the variant name.
        attempt_unify(&self.term, Functor::new(variant, len as u16))?;

        Ok(SerializeNamedTuple {
            context: self.context,
            term: self.term.clone(),
            pos: 0,
        })
    }
    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        Ok(SerializeMap::new(self.context, self.term, None))
    }
    fn serialize_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        // TODO we probably want to have some configurable to make name used in the tag
        Ok(SerializeMap::new(self.context, self.term, None))
    }
    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        Ok(SerializeMap::new(self.context, self.term, Some(variant)))
    }
}

impl ser::Serialize for Atom {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_newtype_struct(ATOM_STRUCT_NAME, &self.atom_ptr())
    }
}

struct AtomEmitter<'a>(Term<'a>);

fn attempt_unify_atom<'a>(term: &Term<'a>, atom_ptr: usize) -> Result<(), Error> {
    let atom = unsafe { Atom::wrap(atom_ptr) };
    let result = attempt_unify(term, &atom);
    std::mem::forget(atom);

    result
}

impl<'a> ser::Serializer for AtomEmitter<'a> {
    type Ok = ();

    type Error = Error;

    type SerializeSeq = Impossible<(), Error>;

    type SerializeTuple = Impossible<(), Error>;

    type SerializeTupleStruct = Impossible<(), Error>;

    type SerializeTupleVariant = Impossible<(), Error>;

    type SerializeMap = Impossible<(), Error>;

    type SerializeStruct = Impossible<(), Error>;

    type SerializeStructVariant = Impossible<(), Error>;

    fn serialize_bool(self, _v: bool) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_i8(self, _v: i8) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_i16(self, _v: i16) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_i32(self, _v: i32) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_i64(self, _v: i64) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_u8(self, _v: u8) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_u16(self, _v: u16) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    #[cfg(target_pointer_width = "32")]
    fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error> {
        attempt_unify_atom(&self.0, v as usize)
    }

    #[cfg(target_pointer_width = "32")]
    fn serialize_u64(self, _v: u64) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    #[cfg(target_pointer_width = "64")]
    fn serialize_u32(self, _v: u32) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    #[cfg(target_pointer_width = "64")]
    fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error> {
        attempt_unify_atom(&self.0, v as usize)
    }

    fn serialize_f32(self, _v: f32) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_f64(self, _v: f64) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_char(self, _v: char) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
        attempt_unify(&self.0, Atomable::Str(v))
    }

    fn serialize_bytes(self, _v: &[u8]) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_some<T: ?Sized>(self, _value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize,
    {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_newtype_struct<T: ?Sized>(
        self,
        _name: &'static str,
        _value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize,
    {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_newtype_variant<T: ?Sized>(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize,
    {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }
}

pub struct SerializeSeq<'a, C: QueryableContextType> {
    context: &'a Context<'a, C>,
    term: Term<'a>,
}

impl<'a, C: QueryableContextType> ser::SerializeSeq for SerializeSeq<'a, C> {
    type Ok = ();

    type Error = Error;

    fn serialize_element<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize,
    {
        if let Some((head, tail)) = attempt_opt(self.context.unify_list_functor(&self.term))? {
            let inner_serializer = Serializer {
                context: self.context,
                term: head,
            };
            value.serialize(inner_serializer)?;
            self.term = tail;

            Ok(())
        } else {
            Err(Error::UnificationFailed)
        }
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        attempt_unify(&self.term, Nil)
    }
}

pub struct SerializeTuple<'a, C: QueryableContextType> {
    context: &'a Context<'a, C>,
    term: Term<'a>,
    len: usize,
}

impl<'a, C: QueryableContextType> ser::SerializeTuple for SerializeTuple<'a, C> {
    type Ok = ();

    type Error = Error;

    fn serialize_element<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize,
    {
        self.len -= 1;
        if self.len == 0 {
            eprintln!("last item");
            // this is our last item, so just unify directly
            let inner_serializer = Serializer {
                context: self.context,
                term: self.term.clone(),
            };
            value.serialize(inner_serializer)
        } else {
            eprintln!("some item");
            attempt_unify(&self.term, functor!(",/2"))?;
            let [head, tail] = attempt_opt(self.context.compound_terms(&self.term))?
                .expect("should have two terms");
            let inner_serializer = Serializer {
                context: self.context,
                term: head,
            };
            value.serialize(inner_serializer)?;

            self.term = tail;

            Ok(())
        }
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        assert!(self.len == 0);

        Ok(())
    }
}

pub struct SerializeNamedTuple<'a, C: QueryableContextType> {
    context: &'a Context<'a, C>,
    term: Term<'a>,
    pos: usize,
}

impl<'a, C: QueryableContextType> SerializeNamedTuple<'a, C> {
    fn serialize_field_impl<T: ?Sized>(&mut self, value: &T) -> Result<(), Error>
    where
        T: Serialize,
    {
        self.pos += 1;

        let term = self.context.new_term_ref();
        // unifying with a variable should always succeed, except for things like resource exceptions
        assert!(attempt(self.term.unify_arg(self.pos, &term))?);

        let inner_serializer = Serializer {
            context: self.context,
            term,
        };
        value.serialize(inner_serializer)?;

        Ok(())
    }
}

impl<'a, C: QueryableContextType> ser::SerializeTupleStruct for SerializeNamedTuple<'a, C> {
    type Ok = ();

    type Error = Error;

    fn serialize_field<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize,
    {
        self.serialize_field_impl(value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(())
    }
}

impl<'a, C: QueryableContextType> ser::SerializeTupleVariant for SerializeNamedTuple<'a, C> {
    type Ok = ();

    type Error = Error;

    fn serialize_field<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize,
    {
        self.serialize_field_impl(value)
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        Ok(())
    }
}

pub struct SerializeMap<'a, C:QueryableContextType> {
    context: &'a Context<'a, C>,
    term: Term<'a>,
    reset_term: Term<'a>,
    builder: DictBuilder<'a>,
    last_key: Option<Key>
}

impl<'a, C:QueryableContextType> SerializeMap<'a, C> {
    fn new(context: &'a Context<'a, C>, term: Term<'a>, tag: Option<&str>) -> Self {
        let reset_term = context.new_term_ref();
        let mut builder = DictBuilder::new();
        if let Some(tag) = tag {
            builder.set_tag(tag);
        }
        Self {
            context,
            term,
            reset_term,
            builder,
            last_key: None
        }
    }
}

impl<'a, C:QueryableContextType> ser::SerializeMap for SerializeMap<'a, C> {
    type Ok = ();

    type Error = Error;

    fn serialize_key<T: ?Sized>(&mut self, key: &T) -> Result<(), Self::Error>
    where
        T: Serialize {
        let serializer = KeyEmitter {
            key: &mut self.last_key,
            getting_atom: false
        };

        key.serialize(serializer)
    }

    fn serialize_value<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize {
        let val_term = self.context.new_term_ref();
        let serializer = Serializer {
            context: self.context,
            term: val_term.clone(),
        };
        value.serialize(serializer)?;
        let mut key = None;
        std::mem::swap(&mut key, &mut self.last_key);
        self.builder.add_entry(key.expect("key should have been set"),
                               val_term);

        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        attempt_unify(&self.term, self.builder)?;
        unsafe { self.reset_term.reset() };

        Ok(())
    }
}

impl<'a, C: QueryableContextType> ser::SerializeStruct for SerializeMap<'a, C> {
    type Ok = ();

    type Error = Error;

    fn serialize_field<T: ?Sized>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), Self::Error>
    where
        T: Serialize {
        let value_term = self.context.new_term_ref();
        let serializer = Serializer {
            context: self.context,
            term: value_term.clone()
        };
        value.serialize(serializer)?;
        self.builder.add_entry(key, value_term);

        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        attempt_unify(&self.term, self.builder)?;
        unsafe { self.reset_term.reset() };

        Ok(())
    }
}

impl<'a, C: QueryableContextType> ser::SerializeStructVariant for SerializeMap<'a, C> {
    type Ok = ();

    type Error = Error;

    fn serialize_field<T: ?Sized>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), Self::Error>
    where
        T: Serialize {
        let value_term = self.context.new_term_ref();
        let serializer = Serializer {
            context: self.context,
            term: value_term.clone()
        };
        value.serialize(serializer)?;
        self.builder.add_entry(key, value_term);

        Ok(())
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        attempt_unify(&self.term, self.builder)?;
        unsafe { self.reset_term.reset() };

        Ok(())
    }
}

struct KeyEmitter<'a> {
    key: &'a mut Option<Key>,
    getting_atom: bool
}

impl<'a> ser::Serializer for KeyEmitter<'a> {
    type Ok = ();

    type Error = Error;

    type SerializeSeq = Impossible<(), Error>;
    type SerializeTuple = Impossible<(), Error>;
    type SerializeTupleStruct = Impossible<(), Error>;
    type SerializeTupleVariant = Impossible<(), Error>;
    type SerializeMap = Impossible<(), Error>;
    type SerializeStruct = Impossible<(), Error>;
    type SerializeStructVariant = Impossible<(), Error>;

    fn serialize_bool(self, v: bool) -> Result<Self::Ok, Self::Error> {
        match v {
            true => *self.key = Some(Key::Atom(atom!("true"))),
            false => *self.key = Some(Key::Atom(atom!("false")))
        }

        Ok(())
    }

    fn serialize_i8(self, v: i8) -> Result<Self::Ok, Self::Error> {
        if v >= 0 {
            self.serialize_u8(v as u8)
        }
        else {
            Err(Error::ValueNotOfExpectedType("key"))
        }
    }

    fn serialize_i16(self, v: i16) -> Result<Self::Ok, Self::Error> {
        if v >= 0 {
            self.serialize_u16(v as u16)
        }
        else {
            Err(Error::ValueNotOfExpectedType("key"))
        }
    }

    fn serialize_i32(self, v: i32) -> Result<Self::Ok, Self::Error> {
        if v >= 0 {
            self.serialize_u32(v as u32)
        }
        else {
            Err(Error::ValueNotOfExpectedType("key"))
        }
    }

    fn serialize_i64(self, v: i64) -> Result<Self::Ok, Self::Error> {
        if v >= 0 {
            self.serialize_u64(v as u64)
        }
        else {
            Err(Error::ValueNotOfExpectedType("key"))
        }
    }

    fn serialize_u8(self, v: u8) -> Result<Self::Ok, Self::Error> {
        *self.key = Some(Key::Int(v as u64));
        Ok(())
    }

    fn serialize_u16(self, v: u16) -> Result<Self::Ok, Self::Error> {
        *self.key = Some(Key::Int(v as u64));
        Ok(())
    }

    #[cfg(target_pointer_width = "32")]
    fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error> {
        if self.getting_atom {
            let atom = unsafe { Atom::wrap(v as atom_t) };
            atom.increment_refcount();
            *self.key = Some(Key::Atom(atom));
        }
        else {
            *self.key = Some(Key::Int(v as u64));
        }
        Ok(())
    }

    #[cfg(target_pointer_width = "32")]
    fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error> {
        *self.key = Some(Key::Int(v));
        Ok(())
    }

    #[cfg(target_pointer_width = "64")]
    fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error> {
        *self.key = Some(Key::Int(v as u64));
        Ok(())
    }

    #[cfg(target_pointer_width = "64")]
    fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error> {
        if self.getting_atom {
            let atom = unsafe { Atom::wrap(v as atom_t) };
            atom.increment_refcount();
            *self.key = Some(Key::Atom(atom));
        }
        else {
            *self.key = Some(Key::Int(v as u64));
        }
        Ok(())
    }

    fn serialize_f32(self, _v: f32) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("key"))
    }

    fn serialize_f64(self, _v: f64) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("key"))
    }

    fn serialize_char(self, v: char) -> Result<Self::Ok, Self::Error> {
        let mut buf = [0u8;4];
        let s = v.encode_utf8(&mut buf);
        *self.key = Some(Key::Atom(Atom::new(s)));
        Ok(())
    }

    fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
        *self.key = Some(Key::Atom(Atom::new(v)));
        Ok(())
    }

    fn serialize_bytes(self, _v: &[u8]) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("key"))
    }

    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("key"))
    }

    fn serialize_some<T: ?Sized>(self, _value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize {
        Err(Error::ValueNotOfExpectedType("key"))
    }

    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("key"))
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("key"))
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        Err(Error::ValueNotOfExpectedType("key"))
    }

    fn serialize_newtype_struct<T: ?Sized>(
        mut self,
        name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize {
        // could be an atom!
        if name == ATOM_STRUCT_NAME {
            self.getting_atom = true;
            value.serialize(self)
        }
        else {
            value.serialize(self)
        }
    }

    fn serialize_newtype_variant<T: ?Sized>(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize {
        Err(Error::ValueNotOfExpectedType("key"))
    }

    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Err(Error::ValueNotOfExpectedType("key"))
    }

    fn serialize_tuple(self, _len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        Err(Error::ValueNotOfExpectedType("key"))
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        Err(Error::ValueNotOfExpectedType("key"))
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        Err(Error::ValueNotOfExpectedType("key"))
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        Err(Error::ValueNotOfExpectedType("key"))
    }

    fn serialize_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        Err(Error::ValueNotOfExpectedType("key"))
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        Err(Error::ValueNotOfExpectedType("key"))
    }
}


#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    #[test]
    fn serialize_u32() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let num: u32 = 42;

        let term = context.new_term_ref();

        to_term(&context, &num, &term).unwrap();

        let term_string = context.string_from_term(&term).unwrap();
        assert_eq!("42", term_string);
    }

    #[test]
    fn serialize_string() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let s = "hello";

        let term = context.new_term_ref();

        to_term(&context, &s, &term).unwrap();

        let term_string = context.string_from_term(&term).unwrap();
        assert_eq!("\"hello\"", term_string);
    }

    #[test]
    fn serialize_atom() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let a = atom!("hello");

        let term = context.new_term_ref();

        to_term(&context, &a, &term).unwrap();

        let term_string = context.string_from_term(&term).unwrap();
        assert_eq!("hello", term_string);
    }

    #[test]
    fn serialize_list() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let list = [42, 43, 44];

        let term = context.new_term_ref();

        to_term(&context, &list.as_slice(), &term).unwrap();

        let term_string = context.string_from_term(&term).unwrap();
        assert_eq!("[42,43,44]", term_string);
    }

    #[test]
    fn serialize_tuple() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let tuple = (42, 43, 44);

        let term = context.new_term_ref();

        to_term(&context, &tuple, &term).unwrap();

        let term_string = context.string_from_term(&term).unwrap();
        assert_eq!("42,43,44", term_string);
    }

    #[test]
    fn serialize_tuple_list() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let list = [42, 43, 44];

        let term = context.new_term_ref();

        to_term(&context, &list, &term).unwrap();

        let term_string = context.string_from_term(&term).unwrap();
        assert_eq!("42,43,44", term_string);
    }

    #[derive(Serialize)]
    #[serde(rename = "flargh")]
    struct Flargh(u64, String, Atom);

    #[test]
    fn serialize_named_tuple() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let flargh = Flargh(42, "hello".to_string(), atom!("moo"));

        let term = context.new_term_ref();
        to_term(&context, &flargh, &term).unwrap();

        let term_string = context.string_from_term(&term).unwrap();
        assert_eq!("flargh(42,\"hello\",moo)", term_string);
    }

    #[test]
    fn serialize_map_with_str_keys() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let map = HashMap::from([("foo", "bar"), ("baz", "quux")]);

        let term = context.new_term_ref();
        to_term(&context, &map, &term).unwrap();

        let return_map: HashMap<Atom, String> = context.deserialize_from_term(&term).unwrap();
        assert_eq!(HashMap::from([(atom!("foo"), "bar".to_string()),
                                  (atom!("baz"), "quux".to_string())]),
                   return_map);
    }

    #[test]
    fn serialize_map_with_atom_keys() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let map = HashMap::from([(atom!("foo"), "bar"), (atom!("baz"), "quux")]);

        let term = context.new_term_ref();
        to_term(&context, &map, &term).unwrap();

        let return_map: HashMap<Atom, String> = context.deserialize_from_term(&term).unwrap();
        assert_eq!(HashMap::from([(atom!("foo"), "bar".to_string()),
                                  (atom!("baz"), "quux".to_string())]),
                   return_map);
    }

    #[test]
    fn serialize_map_with_u8_keys() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let map = HashMap::from([(12u8, "bar"), (42, "quux")]);

        let term = context.new_term_ref();
        to_term(&context, &map, &term).unwrap();

        let return_map: HashMap<u8, String> = context.deserialize_from_term(&term).unwrap();
        assert_eq!(HashMap::from([(12, "bar".to_string()),
                                  (42, "quux".to_string())]),
                   return_map);
    }

    #[test]
    fn serialize_map_with_i8_keys() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let map = HashMap::from([(12i8, "bar"), (42, "quux")]);

        let term = context.new_term_ref();
        to_term(&context, &map, &term).unwrap();

        let return_map: HashMap<u8, String> = context.deserialize_from_term(&term).unwrap();
        assert_eq!(HashMap::from([(12, "bar".to_string()),
                                  (42, "quux".to_string())]),
                   return_map);
    }

    #[derive(Debug, Clone, PartialEq, Serialize, serde::Deserialize)]
    struct AStruct {
        foo: String,
        bar: u32
    }

    #[test]
    fn serialize_struct() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let s = AStruct { foo: "hello".to_string(), bar: 120 };

        let term = context.new_term_ref();
        to_term(&context, &s, &term).unwrap();

        let result: AStruct = context.deserialize_from_term(&term).unwrap();
        assert_eq!(s, result);
    }

    #[derive(Debug, Clone, PartialEq, Serialize, serde::Deserialize)]
    enum EnumStruct {
        Variant1,
        Variant2(String),
        Variant3(String, u32),
        Variant4{foo: String, bar: u32}
    }

    #[test]
    fn serialize_enum_unit_variant() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let v = EnumStruct::Variant1;
        let term = context.new_term_ref();
        to_term(&context, &v, &term).unwrap();
        assert_eq!("'Variant1'", context.string_from_term(&term).unwrap());

        let r: EnumStruct = context.deserialize_from_term(&term).unwrap();
        assert_eq!(r, v);
    }

    #[test]
    fn serialize_enum_newtype_variant() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let v = EnumStruct::Variant2("hello".to_string());
        let term = context.new_term_ref();
        to_term(&context, &v, &term).unwrap();
        assert_eq!("'Variant2'(\"hello\")", context.string_from_term(&term).unwrap());

        let r: EnumStruct = context.deserialize_from_term(&term).unwrap();
        assert_eq!(r, v);
    }

    #[test]
    fn serialize_enum_tuple_variant() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let v = EnumStruct::Variant3("hello".to_string(), 103);
        let term = context.new_term_ref();
        to_term(&context, &v, &term).unwrap();
        assert_eq!("'Variant3'(\"hello\",103)", context.string_from_term(&term).unwrap());

        let r: EnumStruct = context.deserialize_from_term(&term).unwrap();
        assert_eq!(r, v);
    }

    #[test]
    fn serialize_enum_struct_variant() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let v = EnumStruct::Variant4{foo:"hello".to_string(), bar:103};
        let term = context.new_term_ref();
        to_term(&context, &v, &term).unwrap();
        let foo:String = term.get_dict_key("foo").unwrap();
        let bar:u64 = term.get_dict_key("bar").unwrap();
        assert_eq!("hello", foo);
        assert_eq!(103, bar);

        let r: EnumStruct = context.deserialize_from_term(&term).unwrap();
        assert_eq!(r, v);
    }
}
