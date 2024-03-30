use std::fmt;
use std::hash::Hash;

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::array::ArrayType;
use crate::parser::ast::func_sig::FunctionSignature;
use crate::parser::ast::pointer::PointerType;
use crate::parser::ast::r#enum::EnumType;
use crate::parser::ast::r#struct::StructType;
use crate::parser::ast::tuple::TupleType;
use crate::parser::ast::unresolved::UnresolvedType;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};

/// Represents a type referenced in a program.
#[derive(Debug, Clone, Hash, Eq)]
pub enum Type {
    Struct(StructType),
    // TODO: Remove? This only needs to exist here if enums can be declared inline like structs.
    #[allow(dead_code)]
    Enum(EnumType),
    Tuple(TupleType),
    Function(Box<FunctionSignature>),
    Pointer(Box<PointerType>),
    Array(Box<ArrayType>),
    /// Represents a named user-defined (i.e. non-primitive) type.
    Unresolved(UnresolvedType),
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
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

                    args_match && f1.maybe_ret_type == f2.maybe_ret_type
                }
            }
            (Type::Struct(s1), Type::Struct(s2)) => s1 == s2,
            (Type::Enum(s1), Type::Enum(s2)) => s1 == s2,
            (Type::Tuple(t1), Type::Tuple(t2)) => t1 == t2,
            (Type::Pointer(t1), Type::Pointer(t2)) => t1 == t2,
            (Type::Unresolved(u1), Type::Unresolved(u2)) => u1 == u2,
            (_, _) => false,
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Function(fn_sig) => write!(f, "{}", fn_sig),
            Type::Struct(s) => write!(f, "{}", s),
            Type::Enum(s) => write!(f, "{}", s),
            Type::Tuple(t) => write!(f, "{}", t),
            Type::Pointer(t) => write!(f, "{}", t),
            Type::Array(a) => write!(f, "{}", a),
            Type::Unresolved(u) => write!(f, "{}", u.name),
        }
    }
}

impl Locatable for Type {
    fn start_pos(&self) -> &Position {
        match self {
            Type::Struct(struct_type) => struct_type.start_pos(),
            Type::Enum(enum_type) => enum_type.start_pos(),
            Type::Tuple(tuple_type) => tuple_type.start_pos(),
            Type::Function(fn_sig) => fn_sig.start_pos(),
            Type::Pointer(t) => t.start_pos(),
            Type::Array(a) => a.start_pos(),
            Type::Unresolved(unresolved) => unresolved.start_pos(),
        }
    }

    fn end_pos(&self) -> &Position {
        match self {
            Type::Struct(struct_type) => struct_type.end_pos(),
            Type::Enum(enum_type) => enum_type.end_pos(),
            Type::Tuple(tuple_type) => tuple_type.end_pos(),
            Type::Function(fn_sig) => fn_sig.end_pos(),
            Type::Pointer(t) => t.end_pos(),
            Type::Array(a) => a.end_pos(),
            Type::Unresolved(unresolved) => unresolved.end_pos(),
        }
    }
}

impl Type {
    /// Parses a type.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        match tokens.next() {
            Some(Token {
                kind: TokenKind::Fn,
                ..
            }) => {
                tokens.rewind(1);
                let sig = FunctionSignature::from_anon(tokens, false)?;
                Ok(Type::Function(Box::new(sig)))
            }

            Some(Token {
                kind: TokenKind::Struct,
                ..
            }) => {
                tokens.rewind(1);
                let struct_type = StructType::from(tokens)?;
                Ok(Type::Struct(struct_type))
            }

            Some(Token {
                kind: TokenKind::LeftBrace,
                ..
            }) => {
                tokens.rewind(1);
                let tuple_type = TupleType::from(tokens)?;
                Ok(Type::Tuple(tuple_type))
            }

            Some(Token {
                kind: TokenKind::Asterisk,
                ..
            }) => {
                tokens.rewind(1);
                let ptr_type = PointerType::from(tokens)?;
                Ok(Type::Pointer(Box::new(ptr_type)))
            }

            Some(
                ref token @ Token {
                    kind: TokenKind::Identifier(ref type_name),
                    ..
                },
            ) => Ok(Type::Unresolved(UnresolvedType::new(
                type_name.as_str(),
                token.start,
                token.end,
            ))),

            Some(Token {
                kind: TokenKind::LeftBracket,
                ..
            }) => {
                tokens.rewind(1);
                Ok(Type::Array(Box::new(ArrayType::from(tokens)?)))
            }

            Some(other) => {
                return Err(ParseError::new(
                    ErrorKind::ExpectedType,
                    format_code!("expected type, but found {}", other).as_str(),
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

    /// Creates a new unresolved type with the given name.
    pub fn new_unresolved(name: &str) -> Self {
        Type::Unresolved(UnresolvedType::new_with_default_pos(name))
    }
}
