use std::collections::HashSet;

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::parser::error::ParseResult;
use crate::parser::expr::Expression;
use crate::parser::program::Program;
use crate::parser::r#type::Type;
use crate::parser::stream::Stream;

/// Represents a variable declaration. Each variable declaration must have a valid type, a name,
/// and some value as the result of an expression.
#[derive(Debug, PartialEq, Clone)]
pub struct VariableDeclaration {
    pub typ: Option<Type>,
    pub is_mut: bool,
    pub name: String,
    pub value: Expression,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Locatable for VariableDeclaration {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl VariableDeclaration {
    pub fn new(
        typ: Option<Type>,
        is_mut: bool,
        name: String,
        value: Expression,
        start_pos: Position,
        end_pos: Position,
    ) -> Self {
        VariableDeclaration {
            typ,
            is_mut,
            name,
            value,
            start_pos,
            end_pos,
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
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // The first token should be "let".
        let start_token = Program::parse_expecting(tokens, HashSet::from([TokenKind::Let]))?;

        // Parse the optional "mut".
        let is_mut = Program::parse_optional(tokens, HashSet::from([TokenKind::Mut])).is_some();

        // The second token should be the variable name.
        let name = Program::parse_identifier(tokens)?;

        // The colon and variable type are optional.
        let mut typ = None;
        if Program::parse_optional(tokens, HashSet::from([TokenKind::Colon])).is_some() {
            // There was a colon, so there should be a type name.
            typ = Some(Type::from(tokens)?);
        }

        // The remaining tokens should be "=" followed by the variable value.
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Equal]))?;
        let value = Expression::from(tokens, false, false)?;
        let end_pos = value.end_pos().clone();

        Ok(VariableDeclaration::new(
            typ,
            is_mut,
            name,
            value,
            start_token.start,
            end_pos,
        ))
    }
}
