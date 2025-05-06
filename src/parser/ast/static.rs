use crate::lexer::pos::{Locatable, Span};
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::symbol::Name;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::{locatable_impl, util};
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

/// Represents a `static.rs` value declaration.
#[derive(Debug, Eq, Clone)]
pub struct Static {
    pub name: Name,
    pub is_mut: bool,
    pub maybe_type: Option<Type>,
    pub value: Expression,
    pub is_pub: bool,
    pub span: Span,
}

impl Hash for Static {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.maybe_type.hash(state);
        self.value.hash(state);
    }
}

impl PartialEq for Static {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && util::opts_eq(&self.maybe_type, &other.maybe_type)
            && self.value == other.value
    }
}

impl Display for Static {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;

        if let Some(typ) = &self.maybe_type {
            write!(f, ": {}", typ)?;
        }

        write!(f, " = {}", self.value)
    }
}

locatable_impl!(Static);

impl Static {
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        let is_pub = parser.parse_optional(TokenKind::Pub).is_some();
        let start_pos = parser.parse_expecting(TokenKind::Static)?.span.start_pos;
        let is_mut = parser.parse_optional(TokenKind::Mut).is_some();
        let name = Name::parse(parser)?;

        // Parse the optional `: <type>`.
        let typ = match parser.parse_optional(TokenKind::Colon) {
            Some(_) => Some(Type::parse(parser)?),
            None => None,
        };

        // The next token should be `=`.
        parser.parse_expecting(TokenKind::Equal)?;

        // Parse the value as an expression and compute the end position of the statement.
        let value = Expression::parse(parser)?;
        let end_pos = value.span().end_pos;

        Ok(Static {
            name,
            is_mut,
            maybe_type: typ,
            value,
            is_pub,
            span: parser.new_span(start_pos, end_pos),
        })
    }
}
