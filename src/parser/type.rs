use std::fmt;
use std::hash::Hash;

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::bool::BoolType;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::func_sig::FunctionSignature;
use crate::parser::i64::I64Type;
use crate::parser::r#struct::StructType;
use crate::parser::str::StrType;
use crate::parser::stream::Stream;
use crate::parser::tuple::TupleType;
use crate::parser::unresolved::UnresolvedType;
use crate::parser::unsafeptr::UnsafePtrType;
use crate::parser::usize::USizeType;

/// Represents a type referenced in a program.
#[derive(Debug, Clone, Hash, Eq)]
pub enum Type {
    Bool(BoolType),
    Str(StrType),
    I64(I64Type),
    UnsafePtr(UnsafePtrType),
    USize(USizeType),
    Struct(StructType),
    Tuple(TupleType),
    Function(Box<FunctionSignature>),
    /// Represents a named user-defined (i.e. non-primitive) type.
    Unresolved(UnresolvedType),
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Bool(_), Type::Bool(_))
            | (Type::Str(_), Type::Str(_))
            | (Type::I64(_), Type::I64(_))
            | (Type::UnsafePtr(_), Type::UnsafePtr(_))
            | (Type::USize(_), Type::USize(_)) => true,
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
            (Type::Struct(s1), Type::Struct(s2)) => s1 == s2,
            (Type::Tuple(t1), Type::Tuple(t2)) => t1 == t2,
            (Type::Unresolved(u1), Type::Unresolved(u2)) => u1 == u2,
            (_, _) => false,
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Bool(_) => write!(f, "{}", TokenKind::Bool),
            Type::Str(_) => write!(f, "{}", TokenKind::Str),
            Type::I64(_) => write!(f, "{}", TokenKind::I64),
            Type::UnsafePtr(_) => write!(f, "{}", TokenKind::UnsafePtr),
            Type::USize(_) => write!(f, "{}", TokenKind::USize),
            Type::Function(fn_sig) => write!(f, "{}", fn_sig),
            Type::Struct(s) => write!(f, "{}", s),
            Type::Tuple(t) => write!(f, "{}", t),
            Type::Unresolved(u) => write!(f, "{}", u.name),
        }
    }
}

impl Locatable for Type {
    fn start_pos(&self) -> &Position {
        match self {
            Type::Bool(bool_type) => bool_type.start_pos(),
            Type::Str(string_type) => string_type.start_pos(),
            Type::I64(i64_type) => i64_type.start_pos(),
            Type::UnsafePtr(uptr) => uptr.start_pos(),
            Type::USize(usz) => usz.start_pos(),
            Type::Struct(struct_type) => struct_type.start_pos(),
            Type::Tuple(tuple_type) => tuple_type.start_pos(),
            Type::Function(fn_sig) => fn_sig.start_pos(),
            Type::Unresolved(unresolved) => unresolved.start_pos(),
        }
    }

    fn end_pos(&self) -> &Position {
        match self {
            Type::Bool(bool_type) => bool_type.end_pos(),
            Type::Str(string_type) => string_type.end_pos(),
            Type::I64(i64_type) => i64_type.end_pos(),
            Type::UnsafePtr(uptr) => uptr.end_pos(),
            Type::USize(usz) => usz.end_pos(),
            Type::Struct(struct_type) => struct_type.end_pos(),
            Type::Tuple(tuple_type) => tuple_type.end_pos(),
            Type::Function(fn_sig) => fn_sig.end_pos(),
            Type::Unresolved(unresolved) => unresolved.end_pos(),
        }
    }
}

impl Type {
    /// Parses a type.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        match tokens.next() {
            Some(
                token @ Token {
                    kind: TokenKind::Bool,
                    ..
                },
            ) => Ok(Type::Bool(BoolType::new(token.start, token.end))),

            Some(
                token @ Token {
                    kind: TokenKind::I64,
                    ..
                },
            ) => Ok(Type::I64(I64Type::new(token.start, token.end))),

            Some(
                token @ Token {
                    kind: TokenKind::UnsafePtr,
                    ..
                },
            ) => Ok(Type::UnsafePtr(UnsafePtrType::new(token.start, token.end))),

            Some(
                token @ Token {
                    kind: TokenKind::USize,
                    ..
                },
            ) => Ok(Type::USize(USizeType::new(token.start, token.end))),

            Some(
                token @ Token {
                    kind: TokenKind::Str,
                    ..
                },
            ) => Ok(Type::Str(StrType::new(token.start, token.end))),

            Some(
                _token @ Token {
                    kind: TokenKind::Fn,
                    ..
                },
            ) => {
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

    /// Returns a default i64 type.
    pub fn i64() -> Self {
        Type::I64(I64Type::default())
    }

    /// Returns a new unsafeptr type.
    pub fn unsafeptr() -> Self {
        Type::UnsafePtr(UnsafePtrType::default())
    }

    /// Returns a new usize type.
    pub fn usize() -> Self {
        Type::USize(USizeType::default())
    }

    /// Returns a default bool type.
    pub fn bool() -> Self {
        Type::Bool(BoolType::default())
    }

    /// Returns a default str type.
    pub fn str() -> Self {
        Type::Str(StrType::default())
    }

    /// Creates a new unknown type with the given name.
    pub fn new_unknown(name: &str) -> Self {
        Type::Unresolved(UnresolvedType::new_with_default_pos(name))
    }
}
