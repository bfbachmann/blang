use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::r#type::Type;
use crate::parser::error::ParseResult;
use crate::parser::source::Source;
use std::fmt::{Display, Formatter};

/// Represents a pointer to a value of some known type.
#[derive(PartialEq, Clone, Eq, Hash, Debug)]
pub struct PointerType {
    /// The type of the value being pointed to.
    pub pointee_type: Type,
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
    /// Parses a pointer type from the token stream. Expects token sequences of the form
    ///
    ///     `*<type>`
    ///
    /// where
    ///  - `type` is any type (see `Type::from`).
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<PointerType> {
        let start_pos = Source::parse_expecting(tokens, TokenKind::Asterisk)?
            .start
            .clone();
        let pointee_type = Type::from(tokens)?;
        Ok(PointerType {
            start_pos,
            end_pos: pointee_type.end_pos().clone(),
            pointee_type,
        })
    }
}
