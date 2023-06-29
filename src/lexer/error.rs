use std::error::Error;
use std::fmt;

/// Represents any fatal error that occurs during lexing.
#[derive(Debug, PartialEq)]
pub struct LexError {
    pub message: String,
    pub line: usize,
    pub col: usize,
}

impl Error for LexError {}

impl LexError {
    pub fn new(message: &str, line: usize, col: usize) -> Self {
        LexError {
            message: message.to_string(),
            line,
            col,
        }
    }
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Lex error at position [{}:{}]: {}.",
            self.line, self.col, self.message
        )
    }
}
