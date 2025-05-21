use std::fmt::{Display, Formatter};

use crate::lexer::pos::Span;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::r#type::Type;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// Represents a pointer to a value of some known type.
#[derive(PartialEq, Clone, Debug)]
pub struct PointerType {
    /// The type of the value being pointed to.
    pub pointee_type: Type,
    /// Indicates whether the value being pointed to can be mutated via the pointer.
    pub is_mut: bool,
    pub span: Span,
}

impl Display for PointerType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "*{}", self.pointee_type)
    }
}

locatable_impl!(PointerType);

impl PointerType {
    /// Creates a new pointer type.
    pub fn new(pointee_type: Type, is_mut: bool, span: Span) -> PointerType {
        PointerType {
            pointee_type,
            is_mut,
            span,
        }
    }

    /// Creates a new pointer type with default span.
    pub fn new_with_default_span(pointee_type: Type, is_mut: bool) -> PointerType {
        PointerType {
            pointee_type,
            is_mut,
            span: Default::default(),
        }
    }

    /// Parses a pointer type from the token stream. Expects token sequences of the form
    ///
    ///     &type>
    ///     *mut <type>
    ///
    /// where
    ///  - `type` is any type.
    pub fn parse(parser: &mut FileParser) -> ParseResult<PointerType> {
        let start_pos = parser.parse_expecting(TokenKind::Asterisk)?.span.start_pos;
        let is_mut = parser.parse_optional(TokenKind::Mut).is_some();
        let pointee_type = Type::parse(parser)?;
        Ok(PointerType {
            span: parser.new_span(start_pos, pointee_type.span().end_pos),
            pointee_type,
            is_mut,
        })
    }
}
