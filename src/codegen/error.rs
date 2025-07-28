use std::fmt;
use std::fmt::Formatter;

pub type CodeGenResult<T> = Result<T, CodeGenError>;

#[derive(Debug)]
pub enum ErrorKind {
    Optimization,
    WriteOut,
    TargetInit,
    Linking,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ErrorKind::Optimization => write!(f, "optimization failed"),
            ErrorKind::WriteOut => write!(f, "writing output failed"),
            ErrorKind::TargetInit => write!(f, "failed to initialize target"),
            ErrorKind::Linking => write!(f, "linking failed"),
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
