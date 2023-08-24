use std::fmt;
use std::fmt::{Formatter};

pub type CompileResult<T> = Result<T, CompileError>;

#[derive(Debug)]
pub enum ErrorKind {
    InvalidProgram,
    FnVerificationFailed,
    WriteOutFailed,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ErrorKind::InvalidProgram => write!(f, "invalid program"),
            ErrorKind::FnVerificationFailed => write!(f, "function verification failed"),
            ErrorKind::WriteOutFailed => write!(f, "writing output failed"),
        }
    }
}

#[derive(Debug)]
pub struct CompileError {
    kind: ErrorKind,
    message: String,
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.kind, self.message)
    }
}

impl CompileError {
    pub fn new(kind: ErrorKind, message: &str) -> Self {
        CompileError {
            kind,
            message: message.to_string(),
        }
    }
}
