use std::hash::{Hash, Hasher};

use crate::lexer::pos::Span;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// Represents a break statement.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Break {
    pub span: Span,
}

impl Hash for Break {
    fn hash<H: Hasher>(&self, _: &mut H) {
        // Nothing to do here. All breaks should hash to the same value.
    }
}

locatable_impl!(Break);

impl Break {
    /// Parses a break statement from the given token sequence.
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        let token = parser.parse_expecting(TokenKind::Break)?;
        Ok(Break { span: token.span })
    }
}
