use crate::{atom,functor};
use super::*;
use crate::functor::*;
use crate::result::*;
use crate::term::*;
use crate::text::*;
use crate::dict::*;
use serde::Deserialize;
use serde::de::{self, Visitor, MapAccess, SeqAccess, DeserializeSeed};
use std::fmt::{self, Display};

fn from_term<'a, C:QueryableContextType, T>(context: &'a Context<C>, term: &Term<'a>) -> Result<T>
where T: Deserialize<'a> {
    let deserializer = Deserializer {
        context,
        term: term.clone()
    };

    Deserialize::deserialize(deserializer)
}

pub struct Deserializer<'de, C: QueryableContextType> {
    context: &'de Context<'de, C>,
    term: Term<'de>,
}

#[derive(Debug)]
pub enum Error {
    Message(String),
    PrologError(PrologException),
    UnsupportedValue,
    UnexpectedType(&'static str),
    ValueNotOfExpectedType(&'static str),
    ValueOutOfRange
}

impl From<PrologException> for Error {
    fn from(error: PrologException) -> Self {
        Self::PrologError(error)
    }
}

impl Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Message(msg) => formatter.write_str(msg),
            Self::PrologError(_) => formatter.write_str("prolog error"),
            Self::UnsupportedValue => formatter.write_str("unsupported value"),
            Self::UnexpectedType(t) => write!(formatter, "unexpected type {}", t),
            Self::ValueNotOfExpectedType(t) => write!(formatter, "value not of expected type {}", t),
            Self::ValueOutOfRange => formatter.write_str("value out of range"),
        }
    }
}

impl std::error::Error for Error {}

impl de::Error for Error {
    fn custom<T>(msg: T) -> Self
    where
        T: Display,
    {
        Error::Message(msg.to_string())
    }
}


type Result<T> = std::result::Result<T, Error>;

struct DictMapAccess<'de, C:QueryableContextType> {
    context: &'de Context<'de, C>,
    iter: DictIterator<'de, 'de, C>,
    next_value: Option<Term<'de>>
}

impl<'de,C:QueryableContextType> MapAccess<'de> for DictMapAccess<'de,C> {
    type Error = Error;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>>
    where
        K: DeserializeSeed<'de>,
    {
        match self.iter.next() {
            Some((key, value)) => {
                self.next_value = Some(value);

                let inner_de = KeyDeserializer { context: self.context, key };
                seed.deserialize(inner_de).map(Some)
            },
            None => Ok(None)
        }
    }

    fn next_value_seed<K>(&mut self, seed: K) -> Result<K::Value>
    where
        K: DeserializeSeed<'de>,
    {
        let mut next_value = None;
        std::mem::swap(&mut next_value, &mut self.next_value);
        match next_value {
            Some(value) => {
                let inner_de = Deserializer {
                    context: self.context,
                    term: value
                };
                seed.deserialize(inner_de)
            }
            None => panic!("MapAccess used out of order")
        }
    }
}

struct CompoundTermSeqAccess<'a, C:QueryableContextType> {
    context: &'a Context<'a, C>,
    terms: Vec<Term<'a>>
}

impl<'de, C:QueryableContextType> SeqAccess<'de> for CompoundTermSeqAccess<'de, C> {
    type Error = Error;

    fn next_element_seed<T>(&mut self, seed: T) -> std::result::Result<Option<T::Value>, Error>
    where T: DeserializeSeed<'de>
    {
        if let Some(term) = self.terms.pop() {
            let inner_de = Deserializer {
                context: self.context,
                term
            };
            seed.deserialize(inner_de).map(Some)
        }
        else {
            Ok(None)
        }
    }
}

struct CommaCompoundTermSeqAccess<'a, C:QueryableContextType> {
    context: &'a Context<'a, C>,
    term: Term<'a>
}

impl<'de, C:QueryableContextType> SeqAccess<'de> for CommaCompoundTermSeqAccess<'de, C> {
    type Error = Error;

    fn next_element_seed<T>(&mut self, seed: T) -> std::result::Result<Option<T::Value>, Error>
    where T: DeserializeSeed<'de>
    {
        if attempt_opt(self.term.get::<Functor>())? == Some(functor!(",/2")) {
            let [head, tail] = attempt_opt(self.context.compound_terms(&self.term))?.unwrap();
            self.term = tail;
            let inner_de = Deserializer {
                context: self.context,
                term: head
            };
            seed.deserialize(inner_de).map(Some)
        }
        else {
            let inner_de = Deserializer {
                context: self.context,
                term: self.term.clone()
            };
            seed.deserialize(inner_de).map(Some)
        }
    }
}

struct ListSeqAccess<'a, C:QueryableContextType> {
    context: &'a Context<'a, C>,
    iter: TermListIterator<'a, 'a, C>,
}

impl<'de, C:QueryableContextType> SeqAccess<'de> for ListSeqAccess<'de, C> {
    type Error = Error;

    fn next_element_seed<T>(&mut self, seed: T) -> std::result::Result<Option<T::Value>, Error>
    where T: DeserializeSeed<'de>
    {
        if let Some(term) = self.iter.next() {
            let inner_de = Deserializer {
                context: self.context,
                term
            };
            seed.deserialize(inner_de).map(Some)
        }
        else {
            Ok(None)
        }
    }
}

impl<'de, C: QueryableContextType> de::Deserializer<'de> for Deserializer<'de, C> {
    type Error = Error;
    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.term.term_type() {
            TermType::String => self.deserialize_string(visitor),
            _ => Err(Error::UnsupportedValue)
        }
    }
    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match attempt_opt(self.term.get::<Atom>())? {
            Some(atom) =>  {
                if atom == atom!("true") {
                    visitor.visit_bool(true)
                }
                else if atom == atom!("false") {
                    visitor.visit_bool(false)
                }
                else {
                    Err(Error::ValueNotOfExpectedType("bool"))
                }
            },
            None => Err(Error::ValueNotOfExpectedType("bool")),
        }
    }
    fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match attempt_opt(self.term.get::<i64>())? {
            Some(i) => {
                if i >= i8::MIN as i64 && i <= i8::MAX as i64 {
                    visitor.visit_i8(i as i8)
                }
                else {
                    Err(Error::ValueOutOfRange)
                }
            }
            None => Err(Error::ValueNotOfExpectedType("i8"))
        }
    }
    fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match attempt_opt(self.term.get::<i64>())? {
            Some(i) => {
                if i >= i16::MIN as i64 && i <= i16::MAX as i64 {
                    visitor.visit_i16(i as i16)
                }
                else {
                    Err(Error::ValueOutOfRange)
                }
            }
            None => Err(Error::ValueNotOfExpectedType("i16"))
        }
    }
    fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match attempt_opt(self.term.get::<i64>())? {
            Some(i) => {
                if i >= i32::MIN as i64 && i <= i32::MAX as i64 {
                    visitor.visit_i32(i as i32)
                }
                else {
                    Err(Error::ValueOutOfRange)
                }
            }
            None => Err(Error::ValueNotOfExpectedType("i32"))
        }
    }
    fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match attempt_opt(self.term.get::<i64>())? {
            Some(i) => {
                if i >= i64::MIN as i64 && i <= i64::MAX as i64 {
                    visitor.visit_i64(i as i64)
                }
                else {
                    Err(Error::ValueOutOfRange)
                }
            }
            None => Err(Error::ValueNotOfExpectedType("i64"))
        }
    }
    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match attempt_opt(self.term.get::<u64>())? {
            Some(i) => {
                if i <= u8::MAX as u64 {
                    visitor.visit_u8(i as u8)
                }
                else {
                    Err(Error::ValueOutOfRange)
                }
            }
            None => Err(Error::ValueNotOfExpectedType("u8"))
        }
    }
    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match attempt_opt(self.term.get::<u64>())? {
            Some(i) => {
                if i <= u16::MAX as u64 {
                    visitor.visit_u16(i as u16)
                }
                else {
                    Err(Error::ValueOutOfRange)
                }
            }
            None => Err(Error::ValueNotOfExpectedType("u16"))
        }
    }
    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match attempt_opt(self.term.get::<u64>())? {
            Some(i) => {
                if i <= u32::MAX as u64 {
                    visitor.visit_u32(i as u32)
                }
                else {
                    Err(Error::ValueOutOfRange)
                }
            }
            None => Err(Error::ValueNotOfExpectedType("u32"))
        }
    }
    fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match attempt_opt(self.term.get::<u64>())? {
            Some(i) => {
                if i <= u64::MAX as u64 {
                    visitor.visit_u64(i as u64)
                }
                else {
                    Err(Error::ValueOutOfRange)
                }
            }
            None => Err(Error::ValueNotOfExpectedType("u64"))
        }
    }
    fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match attempt_opt(self.term.get::<f64>())? {
            // a little bit suspicious as this loses precision
            Some(f) => visitor.visit_f32(f as f32),
            None => Err(Error::ValueNotOfExpectedType("f32"))
        }
    }
    fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match attempt_opt(self.term.get::<f64>())? {
            // a little bit suspicious as this loses precision
            Some(f) => visitor.visit_f64(f),
            None => Err(Error::ValueNotOfExpectedType("f64"))
        }
    }
    fn deserialize_char<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        // there's two representations in prolog, namely as a single character atom or as a code number
        match self.term.term_type() {
            TermType::Atom => {
                let c = attempt_opt(self.term.get_atom_name(|a| {
                    if a.is_none() {
                        return None;
                    }

                    let mut it = a.unwrap().chars();
                    if let Some(c) = it.next() {
                        if it.next().is_none() {
                            return Some(c);
                        }
                    }

                    None
            }))?.expect("get_atom_name should not fail");
                match c {
                    Some(c) => visitor.visit_char(c),
                    None => Err(Error::ValueNotOfExpectedType("char"))
                }
            },
            TermType::Integer => {
                match attempt_opt(self.term.get::<u64>())? {
                    Some(i) => {
                        if i > u32::MAX as u64 {
                            Err(Error::ValueOutOfRange)
                        }
                        else {
                            match char::from_u32(i as u32) {
                                Some(c) => visitor.visit_char(c),
                                None => Err(Error::ValueOutOfRange)
                            }
                        }
                    },
                    None => Err(Error::ValueNotOfExpectedType("char"))
                }
            },
            _ => Err(Error::ValueNotOfExpectedType("char"))
        }
    }
    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_string(visitor)
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match attempt_opt(self.term.get::<PrologText>())? {
            Some(s) => visitor.visit_string(s.into_inner()),
            None => Err(Error::ValueNotOfExpectedType("string")),
        }
    }
    fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnsupportedValue)
    }
    fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnsupportedValue)
    }
    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        // us being here indicates a value was present.
        visitor.visit_some(self)
    }
    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        if self.term.term_type() == TermType::Nil {
            visitor.visit_unit()
        }
        else {
            Err(Error::ValueNotOfExpectedType("unit"))
        }
    }
    fn deserialize_unit_struct<V>(self, name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_unit(visitor)
    }
    fn deserialize_newtype_struct<V>(self, name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        if name == "$swipl::private::atom" {
            self.deserialize_string(visitor)
        }
        else {
            visitor.visit_newtype_struct(self)
        }
    }
    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let cleanup_term = self.context.new_term_ref();
        let iter = self.context.term_list_iter(&self.term);
        visitor.visit_seq(ListSeqAccess {
            context: self.context,
            iter
        })
    }
    fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let cleanup_term = self.context.new_term_ref();
        let result;
        if attempt_opt(self.term.get::<Functor>())? == Some(functor!(",/2")) {
            result = visitor.visit_seq(CommaCompoundTermSeqAccess {
                context: self.context,
                term: self.term
            });
        }
        else {
            result = match attempt_opt(self.context.compound_terms_vec_sized(&self.term, len))? {
                Some(mut terms) => {
                    terms.reverse();
                    visitor.visit_seq(CompoundTermSeqAccess {
                        context:self.context,
                        terms
                    })
                },
                None => Err(Error::ValueNotOfExpectedType("tuple"))
            };
        }

        unsafe {
            cleanup_term.reset();
        }

        result
    }
    fn deserialize_tuple_struct<V>(
        self,
        name: &'static str,
        len: usize,
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnsupportedValue)
    }
    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        if self.term.term_type() == TermType::Dict {
            visitor.visit_map(DictMapAccess { context: self.context, iter: self.context.dict_entries(&self.term), next_value: None })
        }
        else {
            Err(Error::UnsupportedValue)
        }
    }
    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_map(visitor)
    }
    fn deserialize_enum<V>(
        self,
        name: &'static str,
        variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnsupportedValue)
    }
    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match attempt_opt(self.term.get::<Atom>())? {
            Some(atom) => visitor.visit_string(atom.to_string()),
            None => Err(Error::ValueNotOfExpectedType("identifier"))
        }
    }
    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_none()
    }
}


struct KeyDeserializer<'de, C:QueryableContextType> {
    context: &'de Context<'de, C>,
    key: Key
}

impl<'de, C:QueryableContextType> de::Deserializer<'de> for KeyDeserializer<'de, C> {
    type Error = Error;
    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_string(visitor)
    }
    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.key {
            Key::Atom(atom) => {
                if atom == atom!("true") {
                    visitor.visit_bool(true)
                }
                else if atom == atom!("false") {
                    visitor.visit_bool(false)
                }
                else {
                    Err(Error::ValueNotOfExpectedType("bool"))
                }
            },
            Key::Int(i) => visitor.visit_u64(i)
        }
    }
    fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.key {
            Key::Int(i) => {
                if i <= i8::MAX as u64 {
                    visitor.visit_i8(i as i8)
                }
                else {
                    Err(Error::ValueOutOfRange)
                }
            }
            _ => Err(Error::ValueNotOfExpectedType("i8"))
        }
    }
    fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.key {
            Key::Int(i) => {
                if i <= i16::MAX as u64 {
                    visitor.visit_i16(i as i16)
                }
                else {
                    Err(Error::ValueOutOfRange)
                }
            }
            _ => Err(Error::ValueNotOfExpectedType("i16"))
        }
    }
    fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.key {
            Key::Int(i) => {
                if i <= i32::MAX as u64 {
                    visitor.visit_i32(i as i32)
                }
                else {
                    Err(Error::ValueOutOfRange)
                }
            }
            _ => Err(Error::ValueNotOfExpectedType("i32"))
        }
    }
    fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.key {
            Key::Int(i) => {
                if i <= i64::MAX as u64 {
                    visitor.visit_i64(i as i64)
                }
                else {
                    Err(Error::ValueOutOfRange)
                }
            }
            _ => Err(Error::ValueNotOfExpectedType("i64"))
        }
    }
    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.key {
            Key::Int(i) => {
                if i <= u8::MAX as u64 {
                    visitor.visit_u8(i as u8)
                }
                else {
                    Err(Error::ValueOutOfRange)
                }
            }
            _ => Err(Error::ValueNotOfExpectedType("u8"))
        }
    }
    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.key {
            Key::Int(i) => {
                if i <= u16::MAX as u64 {
                    visitor.visit_u16(i as u16)
                }
                else {
                    Err(Error::ValueOutOfRange)
                }
            }
            _ => Err(Error::ValueNotOfExpectedType("u16"))
        }
    }
    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.key {
            Key::Int(i) => {
                if i <= u32::MAX as u64 {
                    visitor.visit_u32(i as u32)
                }
                else {
                    Err(Error::ValueOutOfRange)
                }
            }
            _ => Err(Error::ValueNotOfExpectedType("u32"))
        }
    }
    fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.key {
            Key::Int(i) => visitor.visit_u64(i),
            _ => Err(Error::ValueNotOfExpectedType("u64"))
        }
    }
    fn deserialize_f32<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnexpectedType("f32"))
    }
    fn deserialize_f64<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnexpectedType("f64"))
    }
    fn deserialize_char<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnexpectedType("char"))
    }
    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_string(visitor)
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.key {
            Key::Atom(a) => visitor.visit_string(a.to_string()),
            // dubious, maybe error
            Key::Int(i) => visitor.visit_string(i.to_string())
        }
    }
    fn deserialize_bytes<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnexpectedType("bytes"))
    }
    fn deserialize_byte_buf<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnexpectedType("byte_buf"))
    }
    fn deserialize_option<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnexpectedType("option"))
    }
    fn deserialize_unit<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnexpectedType("unit"))
    }
    fn deserialize_unit_struct<V>(self, _name: &'static str, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnexpectedType("unit struct"))
    }
    fn deserialize_newtype_struct<V>(self, name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        if name == "$swipl::private::atom" {
            // an atom key!
            self.deserialize_string(visitor)
        }
        else {
            Err(Error::UnexpectedType("newtype struct"))
        }
    }
    fn deserialize_seq<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnexpectedType("seq"))
    }
    fn deserialize_tuple<V>(self, len: usize, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnexpectedType("tuple"))
    }
    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        _len: usize,
        _visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnexpectedType("tuple struct"))
    }
    fn deserialize_map<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnexpectedType("map"))
    }
    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        _visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnexpectedType("struct"))
    }
    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        _visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnexpectedType("enum"))
    }
    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.key {
            Key::Atom(a) => visitor.visit_string(a.to_string()),
            // dubious, maybe error
            Key::Int(i) => visitor.visit_string(i.to_string())
        }
    }
    fn deserialize_ignored_any<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        Err(Error::UnexpectedType("ignored any"))
    }
}

impl<'de> Deserialize<'de> for Atom {
    fn deserialize<D>(deserializer: D) -> std::result::Result<Self, D::Error>
    where D: de::Deserializer<'de> {
        deserializer.deserialize_newtype_struct("$swipl::private::atom", AtomVisitor)
    }
}

struct AtomVisitor;

impl<'de> Visitor<'de> for AtomVisitor {
    type Value = Atom;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "an atom")
    }

    fn visit_str<E>(self, s: &str) -> std::result::Result<Atom, E>
    where E: de::Error {
        Ok(Atom::new(s))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Deserialize;

    #[derive(Deserialize, Debug, PartialEq)]
    struct Baa {
        c: String
    }

    #[derive(Deserialize, Debug, PartialEq)]
    struct Moo {
        a: String,
        b: String,
        baa: Option<Baa>
    }

    #[test]
    fn deserialize_a_struct() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.term_from_string("_{1:\"foo\",a:\"wah\",b:\"bar\", baa: _{c:\"wow\"}}").unwrap();

        let result: Moo = from_term(&context, &term).unwrap();

        assert_eq!(Moo {a: "wah".to_string(),
                        b: "bar".to_string(),
                        baa: Some(Baa { c: "wow".to_string() })},
                   result);
    }

    #[test]
    fn deserialize_an_atom() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.term_from_string("foo").unwrap();

        let result: Atom = from_term(&context, &term).unwrap();

        assert_eq!(atom!("foo"), result);
    }

    use std::collections::HashMap;

    #[test]
    fn deserialize_a_hashmap() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.term_from_string("_{foo:bar,baz:quux}").unwrap();

        let result: HashMap<Atom,Atom> = from_term(&context, &term).unwrap();

        assert_eq!(HashMap::from([(atom!("foo"),atom!("bar")),
                                  (atom!("baz"),atom!("quux"))]),
                   result);
    }

    #[test]
    fn deserialize_a_hashmap_from_number_keys() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.term_from_string("_{10:foo,20:bar}").unwrap();

        let result: HashMap<u8,Atom> = from_term(&context, &term).unwrap();

        assert_eq!(HashMap::from([(10,atom!("foo")),
                                  (20,atom!("bar"))]),
                   result);
    }

    #[test]
    fn deserialize_a_named_tuple() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.term_from_string("foo(a,b,42)").unwrap();

        let result: (Atom, String, u64) = from_term(&context, &term).unwrap();

        assert_eq!((atom!("a"), "b".to_string(), 42),
                   result);
    }

    #[test]
    fn deserialize_an_unnamed_tuple() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.term_from_string("(a,b,42)").unwrap();

        let result: (Atom, String, u64) = from_term(&context, &term).unwrap();

        assert_eq!((atom!("a"), "b".to_string(), 42),
                   result);
    }

    #[test]
    fn deserialize_a_list() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context.term_from_string("(a,b,c)").unwrap();

        let result: [Atom;3] = from_term(&context, &term).unwrap();

        assert_eq!([atom!("a"), atom!("b"), atom!("c")],
                   result);
    }
}
