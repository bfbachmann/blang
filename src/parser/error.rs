use std::fmt;
use std::fmt::{Display, Formatter};

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::locatable_impl;

pub type ParseResult<T> = Result<T, ParseError>;

#[derive(Debug)]
pub enum ErrorKind {
    ExpectedExpr,
    ExpectedExprOrCloseParen,
    ExpectedBasicExpr,
    ExpectedBeginExpr,
    ExpectedBinOpOrEndOfExpr,
    ExpectedIdent,
    ExpectedArgOrEndOfArgs,
    ExpectedType,
    ExpectedModPath,
    UnexpectedOperator,
    UnmatchedCloseParen,
    UnmatchedOpenParen,
    UnexpectedEndOfExpr,
    UnexpectedToken,
    UnexpectedEOF,
    UseOfDoubleNegative,
}

impl Display for ErrorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ErrorKind::ExpectedExpr => write!(f, "expected expression"),
            ErrorKind::ExpectedExprOrCloseParen => write!(f, "expected expression or )"),
            ErrorKind::ExpectedBasicExpr => write!(f, "expected basic expression"),
            ErrorKind::ExpectedBeginExpr => write!(f, "expected beginning of expression"),
            ErrorKind::ExpectedBinOpOrEndOfExpr => {
                write!(f, "expected binary operator or end of expression")
            }
            ErrorKind::ExpectedIdent => write!(f, "expected identifier"),
            ErrorKind::ExpectedArgOrEndOfArgs => write!(f, "expected argument or )"),
            ErrorKind::ExpectedType => write!(f, "expected type"),
            ErrorKind::ExpectedModPath => write!(f, "expected module path"),
            ErrorKind::UnexpectedOperator => write!(f, "expected operator"),
            ErrorKind::UnmatchedCloseParen => write!(f, "unexpected )"),
            ErrorKind::UnmatchedOpenParen => write!(f, "unexpected ("),
            ErrorKind::UnexpectedEndOfExpr => write!(f, "unexpected end of expression"),
            ErrorKind::UnexpectedToken => write!(f, "unexpected token"),
            ErrorKind::UnexpectedEOF => write!(f, "unexpected EOF"),
            ErrorKind::UseOfDoubleNegative => write!(f, "use of double negative"),
        }
    }
}

/// Represents any fatal error that occurs during parsing.
#[derive(Debug)]
pub struct ParseError {
    pub kind: ErrorKind,
    pub message: String,
    pub token: Option<Token>,
    pub start_pos: Position,
    pub end_pos: Position,
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
    pub fn new(
        kind: ErrorKind,
        message: &str,
        token: Option<Token>,
        start_pos: Position,
        end_pos: Position,
    ) -> Self {
        ParseError {
            kind,
            message: message.to_string(),
            token,
            start_pos,
            end_pos,
        }
    }

    pub fn new_with_token(kind: ErrorKind, message: &str, token: Token) -> Self {
        let start_pos = token.start.clone();
        let end_pos = token.end.clone();
        ParseError {
            kind,
            message: message.to_string(),
            token: Some(token),
            start_pos,
            end_pos,
        }
    }
}

locatable_impl!(ParseError);
