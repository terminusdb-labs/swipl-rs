pub mod consts;
pub mod fli;

pub mod atom;
pub mod blob;
pub mod callable;
pub mod context;
pub mod engine;
pub mod functor;
pub mod module;
pub mod predicate;
pub mod result;
pub mod stream;
pub mod term;
pub mod text;

pub mod prelude;

pub use swipl_macros::{
    arc_blob, clone_blob, pred, predicates, prolog, term, wrapped_arc_blob, wrapped_clone_blob,
};
