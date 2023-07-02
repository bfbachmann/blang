use crate::lexer::token::Token;
use std::fmt;

/// Represents any fatal error that occurs during program analysis.
pub struct AnalyzeError {
    message: String,
    token: Option<Token>,
}

impl AnalyzeError {
    pub fn new(message: &str, token: Option<Token>) -> Self {
        AnalyzeError {
            message: message.to_string(),
            token,
        }
    }
}

impl fmt::Display for AnalyzeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Analyze error: {}", self.message)
    }
}
