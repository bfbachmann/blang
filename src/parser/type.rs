use std::collections::VecDeque;

use crate::lexer::kind::TokenKind;
use crate::lexer::token::Token;
use crate::parser::error::ParseError;
use crate::parser::func_sig::FunctionSignature;
use crate::parser::ParseResult;

/// Represents any valid type.
#[derive(Debug, PartialEq)]
pub enum Type {
    Bool,
    String,
    Int,
    Function(Box<FunctionSignature>),
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
                let sig = FunctionSignature::from_anon(tokens)?;
                Ok(Type::Function(Box::new(sig)))
            }
            None => return Err(ParseError::new("Expected type", None)),
            Some(other) => {
                return Err(ParseError::new(
                    format!(r#"Expected type, but got "{}""#, other).as_str(),
                    Some(other),
                ))
            }
        }
    }
}
