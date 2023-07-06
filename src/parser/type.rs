use std::collections::VecDeque;
use std::fmt;

use crate::lexer::kind::TokenKind;
use crate::lexer::token::Token;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::func_sig::FunctionSignature;
use crate::parser::ParseResult;

/// Represents any valid type.
#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    Bool,
    String,
    Int,
    Function(Box<FunctionSignature>),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Bool => write!(f, "bool"),
            Type::String => write!(f, "string"),
            Type::Int => write!(f, "int"),
            Type::Function(fn_sig) => write!(f, "{}", fn_sig),
        }
    }
}

impl Type {
    /// Parses a type.
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        match tokens.pop_front() {
            Some(Token {
                kind: TokenKind::Bool,
                ..
            }) => Ok(Type::Bool),
            Some(Token {
                kind: TokenKind::Int,
                ..
            }) => Ok(Type::Int),
            Some(Token {
                kind: TokenKind::String,
                ..
            }) => Ok(Type::String),
            Some(
                token @ Token {
                    kind: TokenKind::Function,
                    ..
                },
            ) => {
                tokens.push_front(token);
                let sig = FunctionSignature::from_anon(tokens, false)?;
                Ok(Type::Function(Box::new(sig)))
            }
            None => {
                return Err(ParseError::new(
                    ErrorKind::ExpectedType,
                    "Expected type",
                    None,
                ))
            }
            Some(other) => {
                return Err(ParseError::new(
                    ErrorKind::ExpectedType,
                    format!(r#"Expected type, but found "{}""#, other).as_str(),
                    Some(other),
                ))
            }
        }
    }
}
