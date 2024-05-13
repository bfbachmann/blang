use std::fmt::{Display, Formatter};

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::r#type::Type;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;

/// Represents a pointer to a value of some known type.
#[derive(PartialEq, Clone, Eq, Hash, Debug)]
pub struct PointerType {
    /// The type of the value being pointed to.
    pub pointee_type: Type,
    /// Indicates whether the value being pointed to can be mutated via the pointer.
    pub is_mut: bool,
    start_pos: Position,
    end_pos: Position,
}

impl Display for PointerType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "*{}", self.pointee_type)
    }
}

locatable_impl!(PointerType);

impl PointerType {
    /// Creates a new pointer type.
    pub fn new(
        pointee_type: Type,
        is_mut: bool,
        start_pos: Position,
        end_pos: Position,
    ) -> PointerType {
        PointerType {
            pointee_type,
            is_mut,
            start_pos,
            end_pos,
        }
    }

    /// Creates a new pointer type with default start and end positions.
    pub fn new_with_default_pos(pointee_type: Type, is_mut: bool) -> PointerType {
        PointerType {
            pointee_type,
            is_mut,
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Parses a pointer type from the token stream. Expects token sequences of the form
    ///
    ///     &type>
    ///     *mut <type>
    ///
    /// where
    ///  - `type` is any type (see `Type::from`).
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<PointerType> {
        let start_pos = Module::parse_expecting(tokens, TokenKind::Asterisk)?
            .start
            .clone();
        let is_mut = Module::parse_optional(tokens, TokenKind::Mut).is_some();
        let pointee_type = Type::from(tokens)?;
        Ok(PointerType {
            start_pos,
            end_pos: pointee_type.end_pos().clone(),
            pointee_type,
            is_mut,
        })
    }
}
