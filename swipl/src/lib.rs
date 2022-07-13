//! swipl provides a high-level interface to SWI-Prolog. It allows you
//! to write modules or foreign libraries which will be loaded by
//! SWI-Prolog to to provide predicates written in rust. It can also
//! be used to embed SWI-Prolog in a rust application.
//!
//! The code in this crate is divided up into multiple modules. The easiest way to make use of it all is to use the prelude module, which re-exports the contents of all the other modules:
//! ```
//! use swipl::prelude::*;
//! ```
#![doc(html_root_url = "https://terminusdb-labs.github.io/swipl-rs/swipl/")]

pub mod consts;
pub mod fli;

pub mod atom;
pub mod blob;
pub mod callable;
pub mod context;
pub mod dict;
pub mod engine;
pub mod functor;
pub mod init;
pub mod module;
pub mod predicate;
pub mod record;
pub mod result;
pub mod stream;
pub mod term;
pub mod text;

pub mod prelude;

pub use swipl_macros::{
    arc_blob, atom, clone_blob, functor, pred, predicates, prolog, term, wrapped_arc_blob,
    wrapped_clone_blob,
};
