use std::fmt;
use std::fmt::{Display, Formatter};

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;

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
    UnexpectedOperator,
    UnmatchedCloseParen,
    UnmatchedOpenParen,
    UnexpectedEndOfExpr,
    UnexpectedToken,
    UnexpectedEOF,
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
            ErrorKind::UnexpectedToken => write!(f, "unexpected token"),
            ErrorKind::UnexpectedEOF => write!(f, "unexpected EOF"),
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

impl Locatable for ParseError {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}
