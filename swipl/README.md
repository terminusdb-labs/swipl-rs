# swipl-rs swipl crate
This is the central swipl-rs crate, which implements a high-level
interface to SWI-Prolog (wrapping the `swipl-fli` crate), and which
exposes all macros used to generate bindings, foreign predicate
definitions and blob types (exposing the `swipl-macros` crate).

## Building SWI-Prolog foreign libraries
In order to use this library to build something that SWI-Prolog can
use, you have to set your `crate-type` to `cdylib`, and provide a main
function like so:

```rust
#[no_mangle]
pub extern "C" fn install() {
    register_predicate_a();
    register_predicate_b();
    // ..etc
}
```

All predicates defined through the `predicates!` macro have a
corresponding `register_<name>` function, which you'll have to call
inside the `install` function to make this predicate known to
prolog. In addition, you can do whatever else needs to happen at load
time here.

For an example, have a look at [the example project](https://github.com/terminusdb-labs/swipl-rs/tree/master/swipl-module-example).

After building, your foreign library can be loaded in prolog like so:

```prolog
?- use_foreign_library('target/debug/libswipl_module_example.so').
true.
```

(Substitute your project name, and substitute release for debug if you did a release build).

## Testing
At build time, the low-level `swipl-fli` crate will auto-discover your
swipl installation and link against that. The shared objects of this
installation may not be on your path though. In fact, usually they
aren't. This means you cannot just run `cargo test` to run your unit
tests, as this link location is not stored anywhere.

In order to run your unit tests, consider installing `cargo-swipl` like so:
```bash
cargo install cargo-swipl
```

You can then do `cargo swipl test` to run your tests. `cargo-swipl`
will auto-discover your swipl installation in exactly the same way as
the `swipl-fli` build, and adds it to the load path before calling
`cargo test`.
