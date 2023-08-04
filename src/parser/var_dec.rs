use crate::lexer::kind::TokenKind;
use std::collections::{HashSet, VecDeque};

use crate::lexer::token::Token;
use crate::parser::expr::Expression;
use crate::parser::program::Program;
use crate::parser::r#type::Type;

use crate::parser::ParseResult;

/// Represents a variable declaration. Each variable declaration must have a valid type, a name,
/// and some value as the result of an expression.
#[derive(Debug, PartialEq, Clone)]
pub struct VariableDeclaration {
    pub typ: Option<Type>,
    pub name: String,
    pub value: Expression,
}

impl VariableDeclaration {
    pub fn new(typ: Option<Type>, name: String, value: Expression) -> Self {
        VariableDeclaration { typ, name, value }
    }

    /// Parses variable declarations. Expects token sequences of the forms
    ///
    ///     let <name>: <type> = <expr>
    ///     let <name> = <expr>
    ///
    /// where
    ///  - `type` is the variable type
    ///  - `name` is the variable name
    ///  - `expr` is an expression representing the value assigned to the variable
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The first token should be "let".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Let]))?;

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

        Ok(VariableDeclaration::new(typ, name, value))
    }
}
