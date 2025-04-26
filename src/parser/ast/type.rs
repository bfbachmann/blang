use std::fmt;
use std::hash::Hash;

use crate::lexer::pos::{Locatable, Span};
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::array::ArrayType;
use crate::parser::ast::func_sig::FunctionSignature;
use crate::parser::ast::pointer::PointerType;
use crate::parser::ast::symbol::Symbol;
use crate::parser::ast::tuple::TupleType;
use crate::parser::ast::unresolved::UnresolvedType;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;

/// Represents a type referenced in a program.
#[derive(Debug, Clone, Hash, Eq)]
pub enum Type {
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
            Type::Tuple(t) => write!(f, "{}", t),
            Type::Pointer(t) => write!(f, "{}", t),
            Type::Array(a) => write!(f, "{}", a),
            Type::Unresolved(u) => write!(f, "{}", u),
        }
    }
}

impl Locatable for Type {
    fn span(&self) -> &Span {
        match self {
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
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        match parser.tokens.peek_next() {
            Some(Token {
                kind: TokenKind::Fn,
                ..
            }) => {
                let sig = FunctionSignature::parse_anon(parser, false)?;
                Ok(Type::Function(Box::new(sig)))
            }

            Some(Token {
                kind: TokenKind::LeftBrace,
                ..
            }) => {
                let tuple_type = TupleType::parse(parser)?;
                Ok(Type::Tuple(tuple_type))
            }

            Some(Token {
                kind: TokenKind::Asterisk,
                ..
            }) => {
                let ptr_type = PointerType::parse(parser)?;
                Ok(Type::Pointer(Box::new(ptr_type)))
            }

            Some(Token {
                kind: TokenKind::LeftBracket,
                ..
            }) => Ok(Type::Array(Box::new(ArrayType::parse(parser)?))),

            _ => Ok(Type::Unresolved(UnresolvedType::from_symbol(
                Symbol::parse(parser)?,
            ))),
        }
    }

    /// Creates a new unresolved type with the given name.
    pub fn new_unresolved(name: &str) -> Self {
        Type::Unresolved(UnresolvedType::new_with_default_span(name))
    }
}
