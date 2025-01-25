use std::hash::{Hash, Hasher};

use crate::lexer::pos::Span;
use crate::lexer::token_kind::TokenKind;

use crate::locatable_impl;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::r#type::Type;
use crate::parser::error::ParseResult;
use crate::parser::file_parser::FileParser;
use crate::Locatable;

/// Represents a variable declaration. Each variable declaration must have a valid type, a name,
/// and some value as the result of an expression.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableDeclaration {
    pub maybe_type: Option<Type>,
    pub is_mut: bool,
    pub name: String,
    pub value: Expression,
    pub span: Span,
}

impl Hash for VariableDeclaration {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.maybe_type.hash(state);
        self.is_mut.hash(state);
        self.name.hash(state);
        self.value.hash(state);
    }
}

locatable_impl!(VariableDeclaration);

impl VariableDeclaration {
    pub fn new(
        typ: Option<Type>,
        is_mut: bool,
        name: String,
        value: Expression,
        span: Span,
    ) -> Self {
        VariableDeclaration {
            maybe_type: typ,
            is_mut,
            name,
            value,
            span,
        }
    }

    /// Parses variable declarations. Expects token sequences of the forms
    ///
    ///     let <name>: <type> = <expr>
    ///     let mut <name>: <type> = <expr>
    ///     let <name> = <expr>
    ///     let mut <name> = <expr>
    ///
    /// where
    ///  - `type` is the variable type
    ///  - `name` is the variable name
    ///  - `expr` is an expression representing the value assigned to the variable
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        // The first token should be "let".
        let start_token = parser.parse_expecting(TokenKind::Let)?;

        // Parse the optional "mut".
        let is_mut = parser.parse_optional(TokenKind::Mut).is_some();

        // The second token should be the variable name.
        let name = parser.parse_identifier()?;

        // The colon and variable type are optional.
        let mut typ = None;
        if parser.parse_optional(TokenKind::Colon).is_some() {
            // There was a colon, so there should be a type name.
            typ = Some(Type::parse(parser)?);
        }

        // The remaining tokens should be "=" followed by the variable value.
        parser.parse_expecting(TokenKind::Equal)?;
        let value = Expression::parse(parser)?;
        let end_pos = value.span().end_pos;

        Ok(VariableDeclaration::new(
            typ,
            is_mut,
            name,
            value,
            Span {
                file_id: parser.file_id,
                start_pos: start_token.span.start_pos,
                end_pos,
            },
        ))
    }
}
