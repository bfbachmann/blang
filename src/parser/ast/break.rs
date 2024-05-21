use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;

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
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        let token = Module::parse_expecting(tokens, TokenKind::Break)?;
        Ok(Break { span: token.span })
    }
}
