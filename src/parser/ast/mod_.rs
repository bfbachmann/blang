use crate::lexer::pos::Span;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::Locatable;
use std::fmt::Display;
use std::hash::Hash;

/// Represents a module declaration.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ModDecl {
    pub name: String,
    pub span: Span,
}

impl Hash for ModDecl {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
    }
}

impl Display for ModDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "mod {}", self.name)
    }
}

locatable_impl!(ModDecl);

impl ModDecl {
    /// Parses a module declaration from the token stream. Expects token sequences of the form
    ///
    ///     mod <name>
    ///
    /// where `name` is an identifier.
    pub fn parse(parser: &mut FileParser) -> ParseResult<ModDecl> {
        let start_pos = parser.parse_expecting(TokenKind::Mod)?.span.start_pos;
        let name = parser.parse_identifier()?;
        Ok(ModDecl {
            name,
            span: parser.new_span(start_pos, parser.prev_position()),
        })
    }
}
