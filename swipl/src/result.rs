//! Prolog results.
//!
//! Functions in swipl-rs that interact with SWI-Prolog generally
//! return a [PrologResult]. This allows you to use them with the `?`
//! syntax in situations where you need to call multiple such
//! functions, and each failure or exception is a reason to exit
//! early.
//!
//! This module also provides some transformations on prolog results.
use thiserror::Error;

/// A prolog error.
///
/// This is either a failure or an exception. In case of an exception,
/// whowever returned the exception was also supposed to raise an
/// exception on the context.
#[derive(Error, Debug)]
pub enum PrologError {
    #[error("prolog function failed")]
    Failure,
    #[error("prolog function threw an exception")]
    Exception,
}

impl PrologError {
    /// Returns true if this error is a failure.
    pub fn is_failure(&self) -> bool {
        match self {
            PrologError::Failure => true,
            _ => false,
        }
    }

    /// Returns true if this error is an exception.
    pub fn is_exception(&self) -> bool {
        match self {
            PrologError::Exception => true,
            _ => false,
        }
    }
}

/// Unit type for errors which can only be an exception.
#[derive(Debug)]
pub struct PrologException;

impl From<PrologException> for PrologError {
    fn from(_val: PrologException) -> PrologError {
        PrologError::Exception
    }
}

/// The main result type that most interface functions return.
pub type PrologResult<R> = Result<R, PrologError>;
/// Result type for operations that cannot fail, but can throw an exception.
pub type NonFailingPrologResult<R> = Result<R, PrologException>;
/// Result type for expressing failure as a boolean instead of an Err.
pub type BoolPrologResult = Result<bool, PrologException>;
/// result type for expressing failure as an Option type instead of an Err.
pub type OptPrologResult<R> = Result<Option<R>, PrologException>;

/// Transforms a `PrologResult<()>` into a [BoolPrologResult], allowing more easy use from an if block.
///
/// Example:
/// ```
///# use swipl::prelude::*;
///# fn main() -> PrologResult<()> {
///#    let engine = Engine::new();
///#    let activation = engine.activate();
///#    let context: Context<_> = activation.into();
///#
///#    let term = context.new_term_ref();
///     if attempt(term.unify(42_u64))? {
///         // the unification succeeded
///     } else {
///         // the unification failed
///     }
///#    Ok(())
///# }
/// ```
pub fn attempt(r: PrologResult<()>) -> BoolPrologResult {
    match r {
        Ok(()) => Ok(true),
        Err(PrologError::Failure) => Ok(false),
        Err(PrologError::Exception) => Err(PrologException),
    }
}

/// Transforms a [PrologResult] into an [OptPrologResult], allowing more easy use from an if block.
///
/// Example:
/// ```
///# use swipl::prelude::*;
///# fn main() -> PrologResult<()> {
///#    let engine = Engine::new();
///#    let activation = engine.activate();
///#    let context: Context<_> = activation.into();
///#
///#    let term = context.new_term_ref();
///     if let Some(num) = attempt_opt(term.get::<u64>())? {
///         // term contained an u64
///     } else {
///         // term did not contain an u64
///     }
///#    Ok(())
///# }
/// ```
pub fn attempt_opt<R>(r: PrologResult<R>) -> OptPrologResult<R> {
    match r {
        Ok(r) => Ok(Some(r)),
        Err(PrologError::Failure) => Ok(None),
        Err(PrologError::Exception) => Err(PrologException),
    }
}

/// Turn a boolean into a prolog result.
///
/// True will become `Ok(())`, and false will become
/// `Err(PrologError::Failure)`.
pub fn into_prolog_result(b: bool) -> PrologResult<()> {
    match b {
        true => Ok(()),
        false => Err(PrologError::Failure),
    }
}
