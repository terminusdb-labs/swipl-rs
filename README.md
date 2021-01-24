# swipl-rs
Rust bindings to SWI-Prolog.

## Overview
This repository is a workspace for a handful of crates:
- swipl-info: a small utility crate that extracts information about the currently active version of swi-prolog.
- swipl-sys: low-level bindings to SWI-Prolog, generated through bindgen, in a build environment as discovered by swipl-info.
- cargo-swipl: a cargo utility for working with swipl crates. In particular, this allows running of unit tests in crates that depend on swipl-sys.
- swipl: high-level safe bindings to SWI-Prolog.

This is all still in a pretty early state. Implemented so far is prolog engine creation and destruction, term ref creation on those engines, unification and retrieval for a number of terms, and querying prolog from rust. 

Implemented so far:
- engine creation and destruction
- context management
- term ref creation, bound to context lifetimes
- get and unify for a number of rust and prolog types
- prolog calling
- complex term creation from string (through a prolog call)
- easy frontend to `call/1` for easy term calling

To be implemented (roughly in order of delivery):
- get, put, and unify for all common relevant rust and prolog types
- compound term production
- exception handling
- macros for easy foreign predicate writing
- macros for easy blob definitions
- pack generation cargo tool

## Plans
The goal for this project is full native rust packs for SWI-Prolog, without requiring any c glue. A pack in SWI-Prolog is a package that is installable through `pack_install(..)`. There are a few tricky bits towards this goal which I'll list here.

My personal reason for this is that the maintainance of [`terminus_store_prolog`](https://github.com/terminusdb/terminus_store_prolog/) is becoming more and more cumbersome. This project depends heavily on an ever-increasing layer of c glue to marshall rust things into prolog. I greatly desire a reduction of complexity here. 

### Multiple SWI-Prolog environments
There's not necessarily just one SWI-Prolog environment on a particular machine. I myself have about eight different versions installed through `swivm`. The location of these installations may be unpredictable. Therefore we cannot rely on any particular fixed place for the swipl dynamic library in any build scripts, nor is this dynamic library necessarily going to be on the load path.

This is why `swipl-info` exists. This crate will utilize the binary on the path in the `SWIPL` environment variable (which is what SWI-Prolog itself uses while building packages), or lacking that, the `swipl` binary on the path, to query swipl itself about the relevant information.

Furthermore, `cargo-swipl` uses `swipl-info` to provide `cargo swipl test`, a simple frontend for `cargo test` which sets `LD_LIBRARY_PATH` so that the relevant dynamic library can be found. (A similar mechanism will have to be implemented for windows, but is not yet provided).

### Undefined behavior in SWI-Prolog
The SWI-Prolog native interface requires disciplined use. Many calls will result in undefined behavior is care is not taken that preconditions are in place. For example:
- SWI-Prolog must have been initialized
- When working with terms, the engine they were created on is active
- When elements go out of scope (for example term whose frame has been closed), they may no longer be used.

The `swipl` crate intends to prevent all undefined behavior through the compiler where possible, and where not possible, to panic at runtime when a precondition fails. For example, as it is, the `swipl` crate will prevent use of terms whose frame has gone out of scope at compile time, through lifetimes. However, only at runtime will it check that a term is used in the context of the right engine.

## Foreign predicate definition and shared library production
The purpose of a swipl pack written in rust is to provide predicates for swipl that have been written in rust. It is therefore not enough to just have the means to interact with the swipl library. In addition, a native rust module needs to provide an `install()` function where foreign predicates are registered.

It is my intention to implement this through attribute macros and the `cargo-swipl` tool. By marking rust functions with an attribute like `#[swipl:predicate]`, this function can be transformed into something suitable for registering. A command like `cargo swipl pack build` could pick up on these attributes and generate a shim crate with the `install()` function as a very last step in the build process, producing the shared library in the format that SWI-Prolog expects (a .so file on linux, a .dll on windows).
