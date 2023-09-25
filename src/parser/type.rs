use std::fmt;
use std::hash::Hash;

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::parser::bool::BoolType;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::func_sig::FunctionSignature;
use crate::parser::i64::I64Type;
use crate::parser::r#struct::StructType;
use crate::parser::stream::Stream;
use crate::parser::string::StringType;
use crate::parser::tuple::TupleType;
use crate::parser::unresolved::UnresolvedType;
use crate::parser::unsafe_ptr::UnsafePtrType;

/// Represents a type referenced in a program.
#[derive(Debug, Clone, Hash, Eq)]
pub enum Type {
    Bool(BoolType),
    String(StringType),
    I64(I64Type),
    UnsafePtr(UnsafePtrType),
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
            | (Type::String(_), Type::String(_))
            | (Type::I64(_), Type::I64(_))
            | (Type::UnsafePtr(_), Type::UnsafePtr(_)) => true,
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
            Type::Bool(_) => write!(f, "bool"),
            Type::String(_) => write!(f, "string"),
            Type::I64(_) => write!(f, "i64"),
            Type::UnsafePtr(_) => write!(f, "unsafeptr"),
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
            Type::String(string_type) => string_type.start_pos(),
            Type::I64(i64_type) => i64_type.start_pos(),
            Type::UnsafePtr(uptr) => uptr.start_pos(),
            Type::Struct(struct_type) => struct_type.start_pos(),
            Type::Tuple(tuple_type) => tuple_type.start_pos(),
            Type::Function(fn_sig) => fn_sig.start_pos(),
            Type::Unresolved(unresolved) => unresolved.start_pos(),
        }
    }

    fn end_pos(&self) -> &Position {
        match self {
            Type::Bool(bool_type) => bool_type.end_pos(),
            Type::String(string_type) => string_type.end_pos(),
            Type::I64(i64_type) => i64_type.end_pos(),
            Type::UnsafePtr(uptr) => uptr.end_pos(),
            Type::Struct(struct_type) => struct_type.end_pos(),
            Type::Tuple(tuple_type) => tuple_type.end_pos(),
            Type::Function(fn_sig) => fn_sig.end_pos(),
            Type::Unresolved(unresolved) => unresolved.start_pos(),
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
                    kind: TokenKind::String,
                    ..
                },
            ) => Ok(Type::String(StringType::new(token.start, token.end))),

            Some(
                _token @ Token {
                    kind: TokenKind::Function,
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

    /// Returns a default bool type.
    pub fn bool() -> Self {
        Type::Bool(BoolType::default())
    }

    /// Returns a default string type.
    pub fn string() -> Self {
        Type::String(StringType::default())
    }

    /// Creates a new unknown type with the given name.
    pub fn new_unknown(name: &str) -> Self {
        Type::Unresolved(UnresolvedType::new_with_default_pos(name))
    }
}
