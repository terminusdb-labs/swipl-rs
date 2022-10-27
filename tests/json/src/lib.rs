#[cfg(test)]
mod tests {
    use serde::{Deserialize, Serialize};
    use serde_json::{self, json, Value};
    use std::io::{BufWriter, Write};
    use swipl::prelude::*;

    #[test]
    fn deserialize_into_json() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context
            .term_from_string("_{foo: bar, baz: _{elts: [42, _{wow:moo}, 50]}}")
            .unwrap();
        let result: Value = context.deserialize_from_term(&term).unwrap();
        let expected = json!({"foo": "bar",
                              "baz": {"elts": [42,
                                               {"wow":"moo"},
                                               50]}});

        eprintln!("{:?}", result);
        assert_eq!(expected, result);
    }

    #[test]
    fn transcode_into_json() {
        let engine = Engine::new();
        let activation = engine.activate();
        let context: Context<_> = activation.into();

        let term = context
            .term_from_string("_{foo: bar, baz: _{elts: [42, _{wow:moo}, 50]}}")
            .unwrap();

        let buf = BufWriter::new(Vec::new());
        let deserializer = swipl::term::de::Deserializer::new(&context, term.clone());
        let mut serializer = serde_json::Serializer::new(buf);

        serde_transcode::transcode(deserializer, &mut serializer).unwrap();
        let mut buf = serializer.into_inner();
        buf.flush().unwrap();

        let vec = buf.into_inner().unwrap();
        let s = std::str::from_utf8(&vec).unwrap();

        assert_eq!(r#"{"foo":"bar","baz":{"elts":[42,{"wow":"moo"},50]}}"#, s);
    }

    #[derive(Serialize,Deserialize, Debug)]
    struct Foo(usize);

    #[test]
    fn wher() {
        let foo = Foo(42);
        let s = serde_json::to_string(&foo);
        panic!("{:?}", s);
    }

    #[test]
    fn wat() {
        let s = r#"42"#;

        let foo: serde_json::Result<Foo> = serde_json::from_str(s);
        panic!("{:?}", foo);
    }

    #[test]
    fn how() {
        let s = r#"{"Bar":42}"#;
        let foo: serde_json::Result<Value> = serde_json::from_str(s);
        panic!("{:?}", foo);
    }

    #[derive(Serialize,Deserialize,Debug)]
    struct Wow;
    #[test]
    fn unitwah() {
        let s = "null";
        let wow: serde_json::Result<Wow> = serde_json::from_str(s);
        panic!("{:?}", wow);
    }
}
