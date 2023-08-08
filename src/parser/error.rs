use std::fmt;
use std::fmt::{Display, Formatter};

use crate::lexer::token::Token;

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
    UnexpectedOperator,
    UnmatchedCloseParen,
    UnmatchedOpenParen,
    UnexpectedEndOfExpr,
    UnexpectedEndOfArgs,
    UnexpectedToken,
    UnexpectedEndOfStatement,
    InvalidStatement,
    UseOfDoubleNegative,
    DuplicateArgName,
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
            ErrorKind::UnexpectedOperator => write!(f, "expected operator"),
            ErrorKind::UnmatchedCloseParen => write!(f, "unexpected )"),
            ErrorKind::UnmatchedOpenParen => write!(f, "unexpected ("),
            ErrorKind::UnexpectedEndOfExpr => write!(f, "unexpected end of expression"),
            ErrorKind::UnexpectedEndOfArgs => write!(f, "unexpected end of arguments"),
            ErrorKind::UnexpectedToken => write!(f, "unexpected token"),
            ErrorKind::UnexpectedEndOfStatement => write!(f, "unexpected end of statement"),
            ErrorKind::InvalidStatement => write!(f, "invalid statement"),
            ErrorKind::UseOfDoubleNegative => write!(f, "use of double negative"),
            ErrorKind::DuplicateArgName => write!(f, "duplicate argument name"),
        }
    }
}

/// Represents any fatal error that occurs during parsing.
#[derive(Debug)]
pub struct ParseError {
    pub kind: ErrorKind,
    pub message: String,
    pub token: Option<Token>,
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
    pub fn new(kind: ErrorKind, message: &str, token: Option<Token>) -> Self {
        ParseError {
            kind,
            message: message.to_string(),
            token,
        }
    }
}
