# swipl-module-example - an example crate which builds into a foreign library
This project demonstrates how foreign predicates can be defined, and
how they are to be registered. All code is contained in
src/lib.rs. Also, see Cargo.toml to see how the crate-type is set to
`cdylib` to build directly into a loadable object.

After building, the foreign library can be loaded in prolog like so:

```prolog
?- use_foreign_library('target/debug/libswipl_module_example.so').
true.
```
