use std::hash::{Hash, Hasher};

use crate::lexer::pos::Span;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// Represents a continue statement.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Continue {
    pub span: Span,
}

impl Hash for Continue {
    fn hash<H: Hasher>(&self, _: &mut H) {
        // All continue statements are the same, so there's nothing to do here.
    }
}

locatable_impl!(Continue);

impl Continue {
    /// Parses a continue statement from the given token sequence.
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        let token = parser.parse_expecting(TokenKind::Continue)?;
        Ok(Continue { span: token.span })
    }
}
