use std::fmt;
use std::fmt::Formatter;

pub type CodeGenResult<T> = Result<T, CodeGenError>;

#[derive(Debug)]
pub enum ErrorKind {
    OptimizationFailed,
    WriteOutFailed,
    TargetInitFailed,
    LinkingFailed,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ErrorKind::OptimizationFailed => write!(f, "optimization failed"),
            ErrorKind::WriteOutFailed => write!(f, "writing output failed"),
            ErrorKind::TargetInitFailed => write!(f, "failed to initialize target"),
            ErrorKind::LinkingFailed => write!(f, "linking failed"),
        }
    }
}

#[derive(Debug)]
pub struct CodeGenError {
    kind: ErrorKind,
    message: String,
}

impl fmt::Display for CodeGenError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.kind, self.message)
    }
}

impl CodeGenError {
    pub fn new(kind: ErrorKind, message: &str) -> Self {
        CodeGenError {
            kind,
            message: message.to_string(),
        }
    }
}
