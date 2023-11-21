use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::locatable_impl;
use crate::parser::closure::Closure;
use crate::parser::error::ParseResult;
use crate::parser::expr::Expression;
use crate::parser::source::Source;

/// Represents a branch in a conditional. `if` and `elsif` branches must have condition
/// expressions, but `else` branches must not.
#[derive(Debug, PartialEq, Clone)]
pub struct Branch {
    pub condition: Option<Expression>,
    pub body: Closure,
    pub start_pos: Position,
    pub end_pos: Position,
}

locatable_impl!(Branch);

impl Branch {
    /// Creates a new branch.
    pub fn new(
        condition: Option<Expression>,
        body: Closure,
        start_pos: Position,
        end_pos: Position,
    ) -> Self {
        Branch {
            condition,
            body,
            start_pos,
            end_pos,
        }
    }

    /// Parses a branch. If `with_condition` is true, expects token sequences of the form
    ///
    ///     <expr> { ... }
    ///
    /// Otherwise, expects token sequences of the form
    ///
    ///     { ... }
    ///
    /// where
    ///  - `expr` is the branch condition expression (see `Expression::from`)
    pub fn from(tokens: &mut Stream<Token>, with_condition: bool) -> ParseResult<Self> {
        // Record the starting position of the branch.
        let start_pos = Source::current_position(tokens);

        let mut cond_expr = None;
        if with_condition {
            // The following tokens should be an expression that represents the branch condition.
            let expr = Expression::from(tokens, false)?;
            cond_expr = Some(expr);
        }

        // The following tokens should be a closure that contains the statements that would be
        // executed if the branch were taken.
        let body = Closure::from(tokens)?;
        let end_pos = body.end_pos().clone();

        Ok(Branch::new(cond_expr, body, start_pos, end_pos))
    }
}
