use std::hash::{Hash, Hasher};

use crate::lexer::pos::{Locatable, Position, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::locatable_impl;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::op::Operator;
use crate::parser::error::ParseResult;
use crate::parser::module::Module;

/// Represents the assignment of some value (i.e. an expression) to a variable.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VariableAssignment {
    pub target: Expression,
    pub value: Expression,
    span: Span,
}

locatable_impl!(VariableAssignment);

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
            span: Span {
                start_pos,
                end_pos: value.end_pos().clone(),
            },
            target,
            value,
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
    ///     <target> and= <expr>
    ///     <target> or= <expr>
    ///     <target> band= <expr>
    ///     <target> bor= <expr>
    ///     <target> bxor= <expr>
    ///     <target> bls= <expr>
    ///     <target> brs= <expr>
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
                TokenKind::LogicalAndEqual,
                TokenKind::LogicalOrEqual,
                TokenKind::BitwiseAndEqual,
                TokenKind::BitwiseOrEqual,
                TokenKind::BitwiseXorEqual,
                TokenKind::BitwiseLeftShiftEqual,
                TokenKind::BitwiseRightShiftEqual,
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
                    TokenKind::LogicalAndEqual => Operator::LogicalAnd,
                    TokenKind::LogicalOrEqual => Operator::LogicalOr,
                    TokenKind::BitwiseAndEqual => Operator::BitwiseAnd,
                    TokenKind::BitwiseOrEqual => Operator::BitwiseOr,
                    TokenKind::BitwiseXorEqual => Operator::BitwiseXor,
                    TokenKind::BitwiseLeftShiftEqual => Operator::BitwiseLeftShift,
                    TokenKind::BitwiseRightShiftEqual => Operator::BitwiseRightShift,
                    _ => unreachable!(),
                };

                Expression::BinaryOperation(Box::new(target.clone()), op, Box::new(assign_operand))
            }
        };

        Ok(VariableAssignment::new(target, value, start_pos))
    }
}
