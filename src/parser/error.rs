use std::fmt;
use std::fmt::{Display, Formatter};

use crate::lexer::pos::{Locatable, Position, Span};
use crate::lexer::token::Token;
use crate::locatable_impl;

pub type ParseResult<T> = Result<T, ParseError>;

#[derive(Debug, PartialEq)]
pub enum ErrorKind {
    ExpectedExpr,
    ExpectedBasicExpr,
    ExpectedBeginExpr,
    ExpectedIdent,
    InvalidModPath,
    ExpectedStatement,
    UnexpectedEndOfExpr,
    UnexpectedToken,
    UnexpectedEOF,
    #[cfg(not(test))]
    ModNotFound,
}

impl Display for ErrorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ErrorKind::ExpectedExpr => write!(f, "expected expression"),
            ErrorKind::ExpectedBasicExpr => write!(f, "expected basic expression"),
            ErrorKind::ExpectedBeginExpr => write!(f, "expected beginning of expression"),
            ErrorKind::ExpectedIdent => write!(f, "expected identifier"),
            ErrorKind::InvalidModPath => write!(f, "invalid module path"),
            ErrorKind::ExpectedStatement => write!(f, "expected statement"),
            ErrorKind::UnexpectedEndOfExpr => write!(f, "unexpected end of expression"),
            ErrorKind::UnexpectedToken => write!(f, "unexpected token"),
            ErrorKind::UnexpectedEOF => write!(f, "unexpected EOF"),
            #[cfg(not(test))]
            ErrorKind::ModNotFound => write!(f, "module not found"),
        }
    }
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
