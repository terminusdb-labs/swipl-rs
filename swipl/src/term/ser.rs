use crate::functor::Functor;
use crate::{atom, functor};
use crate::context::*;
use crate::result::*;
use super::*;
use super::de::{Error};
use serde::ser::Impossible;
use serde::{self, ser, Serialize};

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
    T: Serialize
{
    let serializer = Serializer {
        context,
        term: term.clone(),
    };

    obj.serialize(serializer)
}

fn attempt_unify<U:Unifiable>(term: &Term, v: U) -> Result<(), Error> {
    if attempt(term.unify(v))? {
        Ok(())
    }
    else {
        Err(Error::UnificationFailed)
    }
}

pub struct Serializer<'a,C:QueryableContextType> {
    context: &'a Context<'a, C>,
    term: Term<'a>,
}

impl<'a, C:QueryableContextType> serde::Serializer for Serializer<'a, C> {
    type Ok = ();
    type Error = Error;
    type SerializeSeq = Self;
    type SerializeTuple = Self;
    type SerializeTupleStruct = Self;
    type SerializeTupleVariant = Self;
    type SerializeMap = Self;
    type SerializeStruct = Self;
    type SerializeStructVariant = Self;

    fn serialize_bool(self, v: bool) -> Result<Self::Ok, Self::Error> {
        attempt_unify(&self.term, v)
    }
    fn serialize_i8(self, v: i8) -> Result<Self::Ok, Self::Error> {
        self.serialize_i64(v as i64)
    }
    fn serialize_i16(self, v: i16)  -> Result<Self::Ok, Self::Error> {
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
                term: term.clone()
            };
            let result = value.serialize(inner_serializer);
            unsafe { term.reset(); }
            result
        }
        else {
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
        name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        if attempt(self.term.unify(Functor::new(name,1)))? {
            let [term] = attempt_opt(self.context.compound_terms(&self.term))?.expect("having just unified the functor with arity 1, retrieving its argument list should have been possible");
            let result = attempt_unify(&term, Atom::new(variant));
            unsafe { term.reset(); }
            result
        }
        else {
            Err(Error::UnificationFailed)
        }
    }
    fn serialize_newtype_struct<T: ?Sized>(
        self,
        name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize,
    {
        if name == "$swipl::private::atom" {
            value.serialize(AtomEmitter(self.term))
        }
        else {
            if attempt(self.term.unify(Functor::new(name,1)))? {
                let [term] = attempt_opt(self.context.compound_terms(&self.term))?.expect("having just unified the functor with arity 1, retrieving its argument list should have been possible");
                let inner_serializer = Serializer { context: self.context, term: term.clone() };
                let result = value.serialize(inner_serializer);
                unsafe { term.reset(); }
                result
            }
            else {
                Err(Error::UnificationFailed)
            }
        }
    }
    fn serialize_newtype_variant<T: ?Sized>(
        self,
        name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize,
    {
        if attempt(self.term.unify(Functor::new(name,1)))? {
            let [term] = attempt_opt(self.context.compound_terms(&self.term))?.expect("having just unified the functor with arity 1, retrieving its argument list should have been possible");
            let result;
            if attempt(term.unify(Functor::new(variant,1)))? {
                let [term] = attempt_opt(self.context.compound_terms(&self.term))?.expect("having just unified the functor with arity 1, retrieving its argument list should have been possible");
                let inner_serializer = Serializer { context: self.context, term: term.clone() };
                result = value.serialize(inner_serializer);
                unsafe { term.reset(); }
            }
            else {
                return Err(Error::UnificationFailed);
            }
            unsafe { term.reset(); }
            result
        }
        else {
            Err(Error::UnificationFailed)
        }
    }
    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        todo!();
    }
    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple, Self::Error> {
        todo!();
    }
    fn serialize_tuple_struct(
        self,
        name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct, Self::Error> {
        todo!();
    }
    fn serialize_tuple_variant(
        self,
        name: &'static str,
        variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleVariant, Self::Error> {
        todo!();
    }
    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
        todo!();
    }
    fn serialize_struct(
        self,
        name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStruct, Self::Error> {
        todo!();
    }
    fn serialize_struct_variant(
        self,
        name: &'static str,
        variant_index: u32,
        variant: &'static str,
        len: usize,
    ) -> Result<Self::SerializeStructVariant, Self::Error> {
        todo!();
    }
}

impl<'a, C:QueryableContextType> ser::SerializeSeq for Serializer<'a, C> {
    type Ok = ();
    type Error = Error;

    fn serialize_element<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize,
    {
        todo!();
    }
    fn end(self) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
}

impl<'a, C:QueryableContextType> ser::SerializeTuple for Serializer<'a, C> {
    type Ok = ();
    type Error = Error;

    fn serialize_element<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize,
    {
        todo!();
    }
    fn end(self) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
}

impl<'a, C:QueryableContextType> ser::SerializeTupleStruct for Serializer<'a, C> {
    type Ok = ();
    type Error = Error;

    fn serialize_field<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize,
    {
        todo!();
    }
    fn end(self) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
}

impl<'a, C:QueryableContextType> ser::SerializeTupleVariant for Serializer<'a, C> {
    type Ok = ();
    type Error = Error;

    fn serialize_field<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize,
    {
        todo!();
    }
    fn end(self) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
}

impl<'a, C:QueryableContextType> ser::SerializeStruct for Serializer<'a, C> {
    type Ok = ();
    type Error = Error;

    fn serialize_field<T: ?Sized>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), Self::Error>
    where
        T: Serialize,
    {
        todo!();
    }
    fn end(self) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
}

impl<'a, C:QueryableContextType> ser::SerializeStructVariant for Serializer<'a, C> {
    type Ok = ();
    type Error = Error;

    fn serialize_field<T: ?Sized>(
        &mut self,
        key: &'static str,
        value: &T,
    ) -> Result<(), Self::Error>
    where
        T: Serialize,
    {
        todo!();
    }
    fn end(self) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
}

impl<'a, C:QueryableContextType> ser::SerializeMap for Serializer<'a, C> {
    type Ok = ();
    type Error = Error;

    fn serialize_key<T: ?Sized>(&mut self, key: &T) -> Result<(), Self::Error>
    where
        T: Serialize {
        todo!()
    }

    fn serialize_value<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize {
        todo!()
    }

    fn end(self) -> Result<Self::Ok, Self::Error> {
        todo!()
    }
}

impl ser::Serialize for Atom {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer {
        serializer.serialize_newtype_struct("$swipl::private::atom",
                                            &self.atom_ptr())
    }
}

struct AtomEmitter<'a>(Term<'a>);

fn attempt_unify_atom<'a>(term: &Term<'a>, atom_ptr: usize) -> Result<(), Error> {
    let atom = unsafe {Atom::wrap(atom_ptr)};
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
        T: Serialize {
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
        T: Serialize {
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
        T: Serialize {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_seq(self, len: Option<usize>) -> Result<Self::SerializeSeq, Self::Error> {
        Err(Error::ValueNotOfExpectedType("string"))
    }

    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple, Self::Error> {
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

    fn serialize_map(self, len: Option<usize>) -> Result<Self::SerializeMap, Self::Error> {
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
