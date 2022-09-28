use super::de::Error;
use serde::{self, ser, Serialize};

impl ser::Error for Error {
    fn custom<T>(c: T) -> Self
    where
        T: std::fmt::Display,
    {
        Self::Message(c.to_string())
    }
}

struct Serializer;

impl serde::Serializer for Serializer {
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
        todo!();
    }
    fn serialize_i8(self, v: i8) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
    fn serialize_i16(self, v: i16) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
    fn serialize_i32(self, v: i32) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
    fn serialize_i64(self, v: i64) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
    fn serialize_u8(self, v: u8) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
    fn serialize_u16(self, v: u16) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
    fn serialize_u32(self, v: u32) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
    fn serialize_u64(self, v: u64) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
    fn serialize_f32(self, v: f32) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
    fn serialize_f64(self, v: f64) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
    fn serialize_char(self, v: char) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
    fn serialize_str(self, v: &str) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
    fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
    fn serialize_none(self) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
    fn serialize_some<T: ?Sized>(self, value: &T) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize,
    {
        todo!();
    }
    fn serialize_unit(self) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
    fn serialize_unit_struct(self, name: &'static str) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
    fn serialize_unit_variant(
        self,
        name: &'static str,
        variant_index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
    fn serialize_newtype_struct<T: ?Sized>(
        self,
        name: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize,
    {
        todo!();
    }
    fn serialize_newtype_variant<T: ?Sized>(
        self,
        name: &'static str,
        variant_index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok, Self::Error>
    where
        T: Serialize,
    {
        todo!();
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

impl ser::SerializeSeq for Serializer {
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

impl ser::SerializeTuple for Serializer {
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

impl ser::SerializeTupleStruct for Serializer {
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

impl ser::SerializeTupleVariant for Serializer {
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

impl ser::SerializeStruct for Serializer {
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

impl ser::SerializeStructVariant for Serializer {
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

impl ser::SerializeMap for Serializer {
    type Ok = ();
    type Error = Error;

    fn serialize_key<T: ?Sized>(&mut self, key: &T) -> Result<(), Self::Error>
    where
        T: Serialize,
    {
        todo!();
    }
    fn serialize_value<T: ?Sized>(&mut self, value: &T) -> Result<(), Self::Error>
    where
        T: Serialize,
    {
        todo!();
    }
    fn end(self) -> Result<Self::Ok, Self::Error> {
        todo!();
    }
}
