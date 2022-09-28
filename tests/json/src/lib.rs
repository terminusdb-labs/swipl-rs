#[cfg(test)]
mod tests {
    use serde_json::{json, Value};
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
}
