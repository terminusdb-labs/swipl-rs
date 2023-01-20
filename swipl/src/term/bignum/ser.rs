impl Serialize for BigInt {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer {
        let s = self.0.to_string();
        serializer.serialize_str(&s)
    }
}

impl Serialize for BigRat {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer {
        let s = self.0.to_string();
        serializer.serialize_str(&s)
    }
}

