use std::fmt;
use std::hash::Hash;

use crate::lexer::pos::{Locatable, Position, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::array::ArrayType;
use crate::parser::ast::func_sig::FunctionSignature;
use crate::parser::ast::pointer::PointerType;
use crate::parser::ast::r#enum::EnumType;
use crate::parser::ast::r#struct::StructType;
use crate::parser::ast::symbol::Symbol;
use crate::parser::ast::tuple::TupleType;
use crate::parser::ast::unresolved::UnresolvedType;
use crate::parser::error::ParseResult;

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
            Type::Unresolved(u) => write!(f, "{}", u),
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

    fn span(&self) -> &Span {
        match self {
            Type::Struct(struct_type) => struct_type.span(),
            Type::Enum(enum_type) => enum_type.span(),
            Type::Tuple(tuple_type) => tuple_type.span(),
            Type::Function(fn_sig) => fn_sig.span(),
            Type::Pointer(t) => t.span(),
            Type::Array(a) => a.span(),
            Type::Unresolved(unresolved) => unresolved.span(),
        }
    }
}

impl Type {
    /// Parses a type.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        match tokens.peek_next() {
            Some(Token {
                kind: TokenKind::Fn,
                ..
            }) => {
                let sig = FunctionSignature::from_anon(tokens, false)?;
                Ok(Type::Function(Box::new(sig)))
            }

            Some(Token {
                kind: TokenKind::Struct,
                ..
            }) => {
                let struct_type = StructType::from(tokens)?;
                Ok(Type::Struct(struct_type))
            }

            Some(Token {
                kind: TokenKind::LeftBrace,
                ..
            }) => {
                let tuple_type = TupleType::from(tokens)?;
                Ok(Type::Tuple(tuple_type))
            }

            Some(Token {
                kind: TokenKind::Asterisk,
                ..
            }) => {
                let ptr_type = PointerType::from(tokens)?;
                Ok(Type::Pointer(Box::new(ptr_type)))
            }

            Some(Token {
                kind: TokenKind::LeftBracket,
                ..
            }) => Ok(Type::Array(Box::new(ArrayType::from(tokens)?))),

            _ => Ok(Type::Unresolved(UnresolvedType::from_symbol(Symbol::from(
                tokens,
            )?))),
        }
    }

    /// Creates a new unresolved type with the given name.
    pub fn new_unresolved(name: &str) -> Self {
        Type::Unresolved(UnresolvedType::new_with_default_pos(name))
    }
}
