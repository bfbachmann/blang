use std::fmt;

use crate::lexer::token::Token;

#[derive(Debug)]
pub enum ErrorKind {
    ExpectedExpr,
    ExpectedExprOrCloseParen,
    ExpectedBasicExpr,
    ExpectedBeginExpr,
    ExpectedBinOpOrEndOfExpr,
    ExpectedIndent,
    ExpectedArgOrEndOfArgs,
    ExpectedType,
    UnexpectedOperator,
    UnmatchedCloseParen,
    UnmatchedOpenParen,
    UnexpectedEndOfExpr,
    UnexpectedExprToken,
    UnexpectedEndOfArgs,
    UnexpectedToken,
    UnexpectedEndOfStatement,
    InvalidStatement,
    UseOfDoubleNegative,
    DuplicateArgName,
}

/// Represents any fatal error that occurs during parsing.
#[derive(Debug)]
pub struct ParseError {
    pub kind: ErrorKind,
    pub message: String,
    pub token: Option<Token>,
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
    pub fn new(kind: ErrorKind, message: &str, token: Option<Token>) -> Self {
        ParseError {
            kind,
            message: message.to_string(),
            token,
        }
    }
}
