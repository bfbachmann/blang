use std::collections::{HashSet, VecDeque};

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::parser::expr::Expression;
use crate::parser::program::Program;
use crate::parser::ParseResult;

/// Represents the assignment of some value (i.e. an expression) to a variable.
#[derive(Debug, PartialEq, Clone)]
pub struct VariableAssignment {
    pub name: String,
    pub value: Expression,
    start_pos: Position,
}

impl Locatable for VariableAssignment {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.value.end_pos()
    }
}

impl VariableAssignment {
    pub fn new(name: &str, value: Expression, start_pos: Position) -> Self {
        VariableAssignment {
            name: name.to_string(),
            value,
            start_pos,
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
        // Get the starting position of the variable assignment.
        let start_pos = Program::current_position(tokens);

        // The next token should be an identifier representing the variable name.
        let name = Program::parse_identifier(tokens)?;

        // The next token should be an assignment "=".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Equal]))?;

        // The next tokens should be some expression.
        let expr = Expression::from(tokens, false, false)?;

        Ok(VariableAssignment::new(name.as_str(), expr, start_pos))
    }
}
