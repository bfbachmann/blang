use std::fmt::{Display, Formatter};

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::r#type::Type;
use crate::parser::source::Source;

/// Represents a `sizeof` statement.
#[derive(Debug, PartialEq, Clone)]
pub struct SizeOf {
    pub typ: Type,
    start_pos: Position,
    end_pos: Position,
}

impl Display for SizeOf {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", TokenKind::SizeOf, self.typ)
    }
}

locatable_impl!(SizeOf);

impl SizeOf {
    /// Parses a `sizeof` statement from the given token sequence. Expects token sequences of the
    /// form
    ///
    ///     sizeof <type>
    ///
    /// where
    ///  - `type` is any type.
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Parse the `sizeof` keyword.
        let sizeof_token = Source::parse_expecting(tokens, TokenKind::SizeOf)?;

        // Parse the type.
        let typ = Type::from(tokens)?;
        let end_pos = typ.end_pos().clone();

        Ok(SizeOf {
            typ,
            start_pos: sizeof_token.start,
            end_pos,
        })
    }
}
