use crate::lexer::Token;
use std::fmt;

/// Represents any fatal error that occurs during parsing.
#[derive(Debug)]
pub struct ParseError {
    message: String,
    token: Option<Token>,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.token {
            Some(token) => write!(f, "Parse error at token {}: {}.", token, self.message),
            None => write!(f, "Parse error: {}.", self.message),
        }
    }
}

impl ParseError {
    pub fn new(message: &str, token: Option<Token>) -> Self {
        ParseError {
            message: message.to_string(),
            token,
        }
    }
}

/// Represents any fatal error that occurs during program analysis.
pub struct AnalyzeError {
    message: String,
}

impl AnalyzeError {
    pub fn new(message: &str) -> Self {
        AnalyzeError {
            message: message.to_string(),
        }
    }
}

impl fmt::Display for AnalyzeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Analyze error: {}", self.message)
    }
}
