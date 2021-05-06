# swipl-rs

![build](https://github.com/terminusdb-labs/swipl-rs/actions/workflows/rust.yml/badge.svg?branch=master)

Rust bindings to SWI-Prolog.

[Documentation](https://terminusdb-labs.github.io/swipl-rs/)

## Using swipl-rs
add the following line under your dependencies in your Cargo.toml file:
```
swipl = "0.3"
```

Then import swipl in your code using
```
use swipl::prelude::*;
```

See the [examples](https://github.com/terminusdb-labs/swipl-rs/tree/master/examples) in this repository and the documentation for more
guidance.


## Overview
This repository is a workspace for a handful of crates:
- cargo-swipl: a cargo utility for working with swipl crates. In particular, this allows running of unit tests in crates that depend on swipl-sys.
- swipl-info: a small utility crate that extracts information about the currently active version of swi-prolog.
- swipl-fli: low-level bindings to SWI-Prolog, generated through bindgen, in a build environment as discovered by swipl-info.
- swipl-macros: procedural macros for generating bindings to prolog predicates, and glue code for defining native prolog predicates.
- swipl: high-level safe bindings to SWI-Prolog.
- swipl-module-example: an example SWI-Prolog foreign library implementation.

Together, they provide an ecosystem for developing swipl foreign libraries, as well as for embedding swipl inside rust applications, without needing any c glue or unsafe code.

## Problems solved
The goal for this project is full native rust packs for SWI-Prolog, without requiring any c glue. A pack in SWI-Prolog is a package that is installable through `pack_install(..)`. There are a few tricky bits towards this goal which I'll list here.

My personal reason for this is that the maintainance of [`terminus_store_prolog`](https://github.com/terminusdb/terminus_store_prolog/) is becoming more and more cumbersome. This project depends heavily on an ever-increasing layer of c glue to marshall rust things into prolog. I greatly desire a reduction of complexity here.

### Multiple SWI-Prolog environments
There's not necessarily just one SWI-Prolog environment on a particular machine. I myself have about eight different versions installed through `swivm`. The location of these installations may be unpredictable. Therefore we cannot rely on any particular fixed place for the swipl dynamic library in any build scripts, nor is this dynamic library necessarily going to be on the load path.

This is why `swipl-info` exists. This crate will utilize the binary on the path in the `SWIPL` environment variable (which is what SWI-Prolog itself uses while building packages), or lacking that, the `swipl` binary on the path, to query swipl itself about the relevant information.

Furthermore, `cargo-swipl` uses `swipl-info` to provide `cargo swipl test`, a simple frontend for `cargo test` which sets the appropriate environment variable (`LD_LIBRARY_PATH` on posix systems, and `PATH` on windows) so that the relevant dynamic library can be found.

### Undefined behavior in SWI-Prolog
The SWI-Prolog native interface requires disciplined use. Many calls will result in undefined behavior is care is not taken that preconditions are in place. For example:
- SWI-Prolog must have been initialized
- When working with terms, the engine they were created on is active
- When elements go out of scope (for example term whose frame has been closed), they may no longer be used.

The `swipl` crate intends to prevent all undefined behavior through the compiler where possible, and where not possible, to panic at runtime when a precondition fails. For example, as it is, the `swipl` crate will prevent use of terms whose frame has gone out of scope at compile time, through lifetimes. However, only at runtime will it check that a term is used in the context of the right engine.

### Easy predicate definitions
Through the power of macros, defining prolog predicates in rust is pretty easy and can be done without requiring you to write any unsafe code. This is done through the `predicate!` macro, which supports both semidet and nondet predicates. See the example module for examples.

## Plans
### Calling into prolog
Calling into prolog is already possible, but the API could be better.

### Integration between async/await and prolog engines
SWI-Prolog implements engines, prolog runtimes which can be suspended and which can move between threads. In the near-future I wish to integrate these engines with rust's async/await mechanism, so that native predicates may be implemented using async/await, causing a prolog engine to suspend and wake up when the native predicate can make progress.

### Foreign predicate definition and shared library production
The purpose of a swipl pack written in rust is to provide predicates for swipl that have been written in rust. It is therefore not enough to just have the means to interact with the swipl library. In addition, a native rust module needs to provide an `install()` function where foreign predicates are registered.

Currently, users of the swipl-rs library have to make their crate compile to cdylib and provide this install method themselves. However, it is my intention to implement an auto-discovery mechanism for all native predicates through the `cargo-swipl` tool. It should be possible to auto-generate a rust file that is to be compiled as cdylib that does all the registry glue.. A command like `cargo swipl module build` could pick up on these attributes and generate a shim crate with the `install()` function as a very last step in the build process, producing the shared library in the format that SWI-Prolog expects (a .so file on linux, a .dll on windows).

### Full pack support
SWI-Prolog expects packs to store their native libraries in particular location which is added to the foreign load path. It also expects an additional `prolog/` directory  containing prolog code, which all packs need, if only to load the foreign code module. Finally it expects a `pack.pl` file containing the pack metadata. `cargo-swipl` should be able to support this format and work with it directly.

- `cargo swipl pack new <pack-name>` - to generate a new stub project with all files in the correct location, a stub prolog file that loads the foreign library, and a Makefile which calls into `cargo swipl pack`.
- `cargo swipl pack build` - to rebuild the pack.
- `cargo swipl pack clean` - to clean the project
