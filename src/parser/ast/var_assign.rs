use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::symbol::Symbol;
use crate::parser::error::ParseResult;
use crate::parser::source::Source;
use std::hash::{Hash, Hasher};

/// Represents the assignment of some value (i.e. an expression) to a variable.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableAssignment {
    pub symbol: Symbol,
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

impl Hash for VariableAssignment {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.symbol.hash(state);
        self.value.hash(state);
    }
}

impl VariableAssignment {
    /// Creates a new variable assignment.
    pub fn new(symbol: Symbol, value: Expression, start_pos: Position) -> Self {
        VariableAssignment {
            symbol,
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
    ///    `Symbol::from`)
    ///  - `expr` is an expression representing the value assigned to the variable
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Get the starting position of the variable assignment.
        let start_pos = Source::current_position(tokens);

        // The next token should be an identifier representing the variable name.
        let var = Symbol::from(tokens)?;

        // The next token should be an assignment "=".
        Source::parse_expecting(tokens, TokenKind::Equal)?;

        // The next tokens should be some expression.
        let expr = Expression::from(tokens, false)?;

        Ok(VariableAssignment::new(var, expr, start_pos))
    }
}
