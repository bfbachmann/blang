
use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::op::Operator;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;

/// Represents the assignment of some value (i.e. an expression) to a variable.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableAssignment {
    pub target: Expression,
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
        self.target.hash(state);
        self.value.hash(state);
    }
}

impl VariableAssignment {
    /// Creates a new variable assignment.
    pub fn new(target: Expression, value: Expression, start_pos: Position) -> Self {
        VariableAssignment {
            target,
            value,
            start_pos,
        }
    }

    /// Parses variable assignments. Expects token sequences of the forms
    ///
    ///     <target> = <expr>
    ///     <target> += <expr>
    ///     <target> -= <expr>
    ///     <target> *= <expr>
    ///     <target> /= <expr>
    ///     <target> %= <expr>
    ///
    /// where
    ///  - `target` is the target that is being assigned to (see `Expression::from`)
    ///  - `expr` is an expression representing the value assigned to the variable
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Self> {
        // Get the starting position of the variable assignment.
        let start_pos = Module::current_position(tokens);

        // The next token should be an expression representing the target to which a value is being assigned.
        let target = Expression::from(tokens)?;

        // The next token should be an assignment operator.
        let assign_op = Module::parse_expecting_any(
            tokens,
            vec![
                TokenKind::Equal,
                TokenKind::PlusEqual,
                TokenKind::MinusEqual,
                TokenKind::AsteriskEqual,
                TokenKind::ForwardSlashEqual,
                TokenKind::PercentEqual,
            ],
        )?
        .kind;

        // The rest should be an expression representing the assigned value or
        // operand.
        let assign_operand = Expression::from(tokens)?;

        let value = match assign_op {
            TokenKind::Equal => assign_operand,
            other => {
                let op = match other {
                    TokenKind::PlusEqual => Operator::Add,
                    TokenKind::MinusEqual => Operator::Subtract,
                    TokenKind::AsteriskEqual => Operator::Multiply,
                    TokenKind::ForwardSlashEqual => Operator::Divide,
                    TokenKind::PercentEqual => Operator::Modulo,
                    _ => unreachable!(),
                };

                Expression::BinaryOperation(Box::new(target.clone()), op, Box::new(assign_operand))
            }
        };

        Ok(VariableAssignment::new(target, value, start_pos))
    }
}
