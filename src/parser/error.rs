use crate::lexer::pos::Span;
use crate::lexer::token::Token;
use crate::locatable_impl;
use crate::Locatable;
use std::fmt;
use std::fmt::{Display, Formatter};

pub type ParseResult<T> = Result<T, ParseError>;

#[derive(Debug, PartialEq)]
pub enum ErrorKind {
    LexError,
    FailedToLocateMod,
    ExpectedExpr,
    ExpectedBasicExpr,
    ExpectedBeginExpr,
    ExpectedIdent,
    InvalidModPath,
    ExpectedStatement,
    UnexpectedEndOfExpr,
    UnexpectedToken,
    UnexpectedEOF,
}

/// Represents any fatal error that occurs during parsing.
#[derive(Debug)]
pub struct ParseError {
    #[allow(dead_code)]
    pub kind: ErrorKind,
    pub message: String,
    pub token: Option<Token>,
    pub span: Span,
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match &self.token {
            Some(token) => write!(f, "parse error at token {}: {}.", token, self.message),
            None => write!(f, "parse error: {}.", self.message),
        }
    }
}

impl ParseError {
    pub fn new(kind: ErrorKind, message: &str, token: Option<Token>, span: Span) -> Self {
        ParseError {
            kind,
            message: message.to_string(),
            token,
            span,
        }
    }

    pub fn new_with_token(kind: ErrorKind, message: &str, token: Token) -> Self {
        let span = token.span;
        ParseError {
            kind,
            message: message.to_string(),
            token: Some(token),
            span,
        }
    }
}

locatable_impl!(ParseError);
