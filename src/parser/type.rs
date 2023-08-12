use std::collections::VecDeque;
use std::fmt;

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::Position;
use crate::lexer::token::Token;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::func_sig::FunctionSignature;
use crate::parser::r#struct::Struct;
use crate::parser::ParseResult;
use crate::util;

/// Represents any valid type.
#[derive(Debug, Clone)]
pub enum Type {
    Bool,
    String,
    I64,
    Struct(Struct),
    Function(Box<FunctionSignature>),
    /// Represents a named user-defined (i.e. non-primitive) type.
    Unresolved(String),
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Bool, Type::Bool) | (Type::String, Type::String) | (Type::I64, Type::I64) => {
                true
            }
            (Type::Function(f1), Type::Function(f2)) => {
                if f1.args.len() != f2.args.len() {
                    false
                } else {
                    let mut args_match = true;
                    for (a1, a2) in f1.args.iter().zip(f2.args.iter()) {
                        if a1.typ != a2.typ {
                            args_match = false;
                        }
                    }

                    args_match && f1.return_type == f2.return_type
                }
            }
            (Type::Struct(s1), Type::Struct(s2)) => {
                s1.name == s2.name && util::vectors_are_equal(&s1.fields, &s2.fields)
            }
            (_, _) => false,
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Bool => write!(f, "bool"),
            Type::String => write!(f, "string"),
            Type::I64 => write!(f, "int"),
            Type::Function(fn_sig) => write!(f, "{}", fn_sig),
            Type::Struct(s) => write!(f, "{}", s),
            Type::Unresolved(name) => write!(f, "{}", name),
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
                kind: TokenKind::I64,
                ..
            }) => Ok(Type::I64),

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

            Some(
                token @ Token {
                    kind: TokenKind::Struct,
                    ..
                },
            ) => {
                tokens.push_front(token);
                let struct_type = Struct::from(tokens)?;
                Ok(Type::Struct(struct_type))
            }

            Some(Token {
                kind: TokenKind::Identifier(type_name),
                ..
            }) => Ok(Type::Unresolved(type_name)),

            Some(other) => {
                return Err(ParseError::new(
                    ErrorKind::ExpectedType,
                    format!(r#"expected type, but found "{}""#, other).as_str(),
                    Some(other.clone()),
                    other.start,
                    other.end,
                ))
            }

            None => {
                return Err(ParseError::new(
                    ErrorKind::UnexpectedEOF,
                    "expected type, but found EOF",
                    None,
                    Position::default(),
                    Position::default(),
                ))
            }
        }
    }
}
