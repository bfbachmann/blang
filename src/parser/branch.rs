use crate::lexer::kind::TokenKind;
use crate::lexer::Token;
use crate::parser::closure::Closure;
use crate::parser::expr::Expression;
use crate::parser::ParseResult;
use std::collections::{HashSet, VecDeque};

/// Represents a branch in a conditional. "if" and "else if" branches must have condition
/// expressions, but "else" branches must not.
#[derive(Debug, PartialEq)]
pub struct Branch {
    condition: Option<Expression>,
    body: Closure,
}

impl Branch {
    pub fn new(condition: Option<Expression>, body: Closure) -> Self {
        Branch { condition, body }
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
    pub fn from(tokens: &mut VecDeque<Token>, with_condition: bool) -> ParseResult<Self> {
        let mut cond_expr = None;
        if with_condition {
            // The following tokens should be an expression that represents the branch condition.
            let (expr, terminator) =
                Expression::from(tokens, HashSet::from([TokenKind::BeginClosure]))?;
            cond_expr = Some(expr);

            // Put the "{" token back because closure parsing requires it.
            tokens.push_front(terminator);
        }

        // The following tokens should be a closure that contains the statements that would be
        // executed if the branch were taken.
        let body = Closure::from(tokens)?;

        Ok(Branch::new(cond_expr, body))
    }
}
