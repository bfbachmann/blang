use std::collections::HashSet;

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::parser::error::ParseResult;
use crate::parser::expr::Expression;
use crate::parser::program::Program;
use crate::parser::stream::Stream;
use crate::parser::var::Var;

/// Represents the assignment of some value (i.e. an expression) to a variable.
#[derive(Debug, PartialEq, Clone)]
pub struct VariableAssignment {
    pub var: Var,
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
    /// Creates a new variable assignment.
    pub fn new(var: Var, value: Expression, start_pos: Position) -> Self {
        VariableAssignment {
            var,
            value,
            start_pos,
        }
    }

    /// Parses variable assignments. Expects token sequences of the form
    ///
    ///     <var> = <expr>
    ///
    /// where
    ///  - `var` is the variable name or a field access (e.g. `var.field.subfield`, see
    ///    `Var::from`)
    ///  - `expr` is an expression representing the value assigned to the variable
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Get the starting position of the variable assignment.
        let start_pos = Program::current_position(tokens);

        // The next token should be an identifier representing the variable name.
        let var = Var::from(tokens)?;

        // The next token should be an assignment "=".
        Program::parse_expecting(tokens, HashSet::from([TokenKind::Equal]))?;

        // The next tokens should be some expression.
        let expr = Expression::from(tokens, false, false)?;

        Ok(VariableAssignment::new(var, expr, start_pos))
    }
}
