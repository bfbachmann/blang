use core::fmt;

use crate::lexer::kind::TokenKind;

/// Represents an operator.
#[derive(Debug, PartialEq)]
pub enum Operator {
    // Basic binary operators
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    LogicalAnd,
    LogicalOr,

    // Basic unary operators
    Not,

    // Comparators
    EqualTo,
    NotEqualTo,
    GreaterThan,
    LessThan,
    GreaterThanOrEqual,
    LessThanOrEqual,
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
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
            TokenKind::Not => Some(Operator::Not),
            TokenKind::EqualTo => Some(Operator::EqualTo),
            TokenKind::NotEqualTo => Some(Operator::NotEqualTo),
            TokenKind::GreaterThan => Some(Operator::GreaterThan),
            TokenKind::LessThan => Some(Operator::LessThan),
            TokenKind::GreaterThanOrEqual => Some(Operator::GreaterThanOrEqual),
            TokenKind::LessThanOrEqual => Some(Operator::LessThanOrEqual),
            _ => None,
        }
    }

    pub fn to_string(&self) -> String {
        match self {
            Operator::Add => "+".to_string(),
            Operator::Subtract => "-".to_string(),
            Operator::Multiply => "*".to_string(),
            Operator::Divide => "/".to_string(),
            Operator::Modulo => "%".to_string(),
            Operator::LogicalAnd => "&&".to_string(),
            Operator::LogicalOr => "||".to_string(),
            Operator::Not => "!".to_string(),
            Operator::EqualTo => "==".to_string(),
            Operator::NotEqualTo => "!=".to_string(),
            Operator::GreaterThan => ">".to_string(),
            Operator::LessThan => "<".to_string(),
            Operator::GreaterThanOrEqual => ">=".to_string(),
            Operator::LessThanOrEqual => "<=".to_string(),
        }
    }
}
