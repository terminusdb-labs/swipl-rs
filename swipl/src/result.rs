use thiserror::Error;

#[derive(Error, Debug)]
pub enum PrologError {
    #[error("prolog function failed")]
    Failure,
    #[error("prolog function threw an exception")]
    Exception,
}

impl PrologError {
    pub fn is_failure(&self) -> bool {
        match self {
            PrologError::Failure => true,
            _ => false,
        }
    }

    pub fn is_exception(&self) -> bool {
        match self {
            PrologError::Exception => true,
            _ => false,
        }
    }
}

#[derive(Debug)]
pub struct PrologException;

impl From<PrologException> for PrologError {
    fn from(_val: PrologException) -> PrologError {
        PrologError::Exception
    }
}

pub type PrologResult<R> = Result<R, PrologError>;
pub type BoolPrologResult = Result<bool, PrologException>;
pub type OptPrologResult<R> = Result<Option<R>, PrologException>;

pub fn attempt(r: PrologResult<()>) -> BoolPrologResult {
    match r {
        Ok(()) => Ok(true),
        Err(PrologError::Failure) => Ok(false),
        Err(PrologError::Exception) => Err(PrologException),
    }
}

pub fn attempt_opt<R>(r: PrologResult<R>) -> OptPrologResult<R> {
    match r {
        Ok(r) => Ok(Some(r)),
        Err(PrologError::Failure) => Ok(None),
        Err(PrologError::Exception) => Err(PrologException),
    }
}

pub fn into_prolog_result(b: bool) -> PrologResult<()> {
    match b {
        true => Ok(()),
        false => Err(PrologError::Failure),
    }
}
