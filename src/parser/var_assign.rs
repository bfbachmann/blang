use std::collections::{HashSet, VecDeque};

use crate::lexer::kind::TokenKind;
use crate::lexer::token::Token;
use crate::parser::expr::Expression;
use crate::parser::program::Program;
use crate::parser::ParseResult;

/// Represents the assignment of some value (i.e. an expression) to a variable.
#[derive(Debug, PartialEq)]
pub struct VariableAssignment {
    pub name: String,
    pub value: Expression,
}

impl VariableAssignment {
    pub fn new(name: &str, value: Expression) -> Self {
        VariableAssignment {
            name: name.to_string(),
            value,
        }
    }

    /// Parses variable assignments. Expects token sequences of the form
    ///
    ///     <name> = <expr>
    ///
    /// where
    ///  - `name` is the variable name
    ///  - `expr` is an expression representing the value assigned to the variable
    pub fn from(tokens: &mut VecDeque<Token>) -> ParseResult<Self> {
        // The next token should be an identifier representing the variable name.
        let name = Program::parse_identifier(tokens)?;

        // The next token should be an assignment "=".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Equal]))?;

        // The next tokens should be some expression.
        let expr = Expression::from(tokens, false)?;

        Ok(VariableAssignment::new(name.as_str(), expr))
    }
}