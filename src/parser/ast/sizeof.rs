use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::lexer::pos::Span;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::r#type::Type;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// Represents a `sizeof` statement. Note that `sizeof` expressions are not
/// considered unary operations (i.e. `sizeof` is not an operator) because
/// the would-be operand is a type rather than an expression.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SizeOf {
    pub typ: Type,
    pub span: Span,
}

impl Display for SizeOf {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", TokenKind::SizeOf, self.typ)
    }
}

impl Hash for SizeOf {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.typ.hash(state);
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
    pub fn from(parser: &mut FileParser) -> ParseResult<Self> {
        // Parse the `sizeof` keyword.
        let sizeof_token = parser.parse_expecting(TokenKind::SizeOf)?;

        // Parse the type.
        let typ = Type::parse(parser)?;
        let end_pos = typ.span().end_pos;

        Ok(SizeOf {
            typ,
            span: parser.new_span(sizeof_token.span.start_pos, end_pos),
        })
    }
}
