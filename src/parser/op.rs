use crate::lexer::kind::TokenKind;

/// Represents an operator.
#[derive(Debug, PartialEq)]
pub enum Operator {
    // Basic operators
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    LogicalAnd,
    LogicalOr,

    // Comparators
    Equals,
    GreaterThan,
    LessThan,
    GreaterThanOrEqual,
    LessThanOrEqual,
}

impl Operator {
    // Creates an operator from the given token kind. Returns `None` if the kind is not a valid
    // operator.
    pub fn from(kind: &TokenKind) -> Option<Self> {
        match kind {
            TokenKind::Add => Some(Operator::Add),
            TokenKind::Subtract => Some(Operator::Subtract),
            TokenKind::Multiply => Some(Operator::Multiply),
            TokenKind::Divide => Some(Operator::Divide),
            TokenKind::Modulo => Some(Operator::Modulo),
            TokenKind::LogicalAnd => Some(Operator::LogicalAnd),
            TokenKind::LogicalOr => Some(Operator::LogicalOr),
            TokenKind::Equals => Some(Operator::Equals),
            TokenKind::GreaterThan => Some(Operator::GreaterThan),
            TokenKind::LessThan => Some(Operator::LessThan),
            TokenKind::GreaterThanOrEqual => Some(Operator::GreaterThanOrEqual),
            TokenKind::LessThanOrEqual => Some(Operator::LessThanOrEqual),
            _ => None,
        }
    }
}
