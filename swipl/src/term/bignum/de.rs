impl<'de> Deserialize<'de> for BigInt {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de> {
        deserializer.deserialize_str(BigIntDeserializationVisitor)
    }
}

struct BigIntDeserializationVisitor;

impl<'de> Visitor<'de> for BigIntDeserializationVisitor {
    type Value = BigInt;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "bigint")
    }

    fn visit_str<E:Error>(self, v: &str) -> Result<BigInt, E> {
        Integer::from_str(v)
            .map(|i| BigInt(i))
            .map_err(|_e| E::custom(format!("{v} did not parse to a bigint")))
    }
}

impl<'de> Deserialize<'de> for BigRat {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de> {
        deserializer.deserialize_str(BigRatDeserializationVisitor)
    }
}

struct BigRatDeserializationVisitor;

impl<'de> Visitor<'de> for BigRatDeserializationVisitor {
    type Value = BigRat;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "bigrat")
    }

    fn visit_str<E:Error>(self, v: &str) -> Result<BigRat, E> {
        Rational::from_str(v)
            .map(|i| BigRat(i))
            .map_err(|_e| E::custom(format!("{v} did not parse to a bigrat")))
    }
}
