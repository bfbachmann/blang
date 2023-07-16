use core::fmt;

use crate::lexer::kind::TokenKind;

/// Represents an operator.
#[derive(Debug, PartialEq, Clone)]
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

    // Other
    LeftParen,
    RightParen,
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl Operator {
    /// Creates an operator from the given token kind. Returns `None` if the kind is not a valid
    /// operator.
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
            TokenKind::LeftParen => Some(Operator::LeftParen),
            TokenKind::RightParen => Some(Operator::RightParen),
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
            Operator::LeftParen => "(".to_string(),
            Operator::RightParen => ")".to_string(),
        }
    }

    /// Returns the precedence of this operator. Relative operator precedence is copied from the C
    /// standard.
    pub fn precedence(&self) -> u32 {
        100 - match self {
            Operator::LeftParen | Operator::RightParen => 1,
            Operator::Not => 2,
            Operator::Multiply | Operator::Divide | Operator::Modulo => 3,
            Operator::Add | Operator::Subtract => 4,
            Operator::GreaterThan
            | Operator::LessThan
            | Operator::GreaterThanOrEqual
            | Operator::LessThanOrEqual => 6,
            Operator::EqualTo | Operator::NotEqualTo => 7,
            Operator::LogicalAnd => 11,
            Operator::LogicalOr => 12,
        }
    }

    /// Returns true if the operator is left-associative. Operator associativity is copied from
    /// the C standard.
    pub fn is_left_associative(&self) -> bool {
        match self {
            Operator::Not => false,
            _ => true,
        }
    }

    /// Returns true if this is a binary operator.
    pub fn is_binary(&self) -> bool {
        match self {
            Operator::Not => false,
            _ => true,
        }
    }

    /// Returns true if the operator is an arithmetic binary operator.
    pub fn is_arithmetic(&self) -> bool {
        matches!(
            self,
            Operator::Add
                | Operator::Subtract
                | Operator::Multiply
                | Operator::Divide
                | Operator::Modulo
        )
    }

    /// Returns true if the operator is a binary comparator.
    pub fn is_comparator(&self) -> bool {
        matches!(
            self,
            Operator::EqualTo
                | Operator::NotEqualTo
                | Operator::GreaterThan
                | Operator::LessThan
                | Operator::GreaterThanOrEqual
                | Operator::LessThanOrEqual
        )
    }

    /// Returns true if the operator is a binary logical operator..
    pub fn is_logical(&self) -> bool {
        matches!(self, Operator::LogicalAnd | Operator::LogicalOr)
    }
}
