use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;

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
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let token = Module::parse_expecting(tokens, TokenKind::Continue)?;
        Ok(Continue { span: token.span })
    }
}
