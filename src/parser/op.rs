use core::fmt;

use crate::lexer::token_kind::TokenKind;

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
    As,

    // Basic unary operators
    LogicalNot,

    // Comparators
    EqualTo,
    Like,
    NotLike,
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
            TokenKind::LogicalNot => Some(Operator::LogicalNot),
            TokenKind::EqualTo => Some(Operator::EqualTo),
            TokenKind::NotEqualTo => Some(Operator::NotEqualTo),
            TokenKind::GreaterThan => Some(Operator::GreaterThan),
            TokenKind::LessThan => Some(Operator::LessThan),
            TokenKind::GreaterThanOrEqual => Some(Operator::GreaterThanOrEqual),
            TokenKind::LessThanOrEqual => Some(Operator::LessThanOrEqual),
            TokenKind::LeftParen => Some(Operator::LeftParen),
            TokenKind::RightParen => Some(Operator::RightParen),
            TokenKind::As => Some(Operator::As),
            TokenKind::Like => Some(Operator::Like),
            TokenKind::NotLike => Some(Operator::NotLike),
            _ => None,
        }
    }

    pub fn to_string(&self) -> String {
        match self {
            Operator::Add => TokenKind::Add.to_string(),
            Operator::Subtract => TokenKind::Subtract.to_string(),
            Operator::Multiply => TokenKind::Multiply.to_string(),
            Operator::Divide => TokenKind::Divide.to_string(),
            Operator::Modulo => TokenKind::Modulo.to_string(),
            Operator::LogicalAnd => TokenKind::LogicalAnd.to_string(),
            Operator::LogicalOr => TokenKind::LogicalOr.to_string(),
            Operator::LogicalNot => TokenKind::LogicalNot.to_string(),
            Operator::EqualTo => TokenKind::EqualTo.to_string(),
            Operator::Like => TokenKind::Like.to_string(),
            Operator::NotLike => TokenKind::NotLike.to_string(),
            Operator::NotEqualTo => TokenKind::NotEqualTo.to_string(),
            Operator::GreaterThan => TokenKind::GreaterThan.to_string(),
            Operator::LessThan => TokenKind::LessThan.to_string(),
            Operator::GreaterThanOrEqual => TokenKind::GreaterThanOrEqual.to_string(),
            Operator::LessThanOrEqual => TokenKind::LessThanOrEqual.to_string(),
            Operator::LeftParen => TokenKind::LeftParen.to_string(),
            Operator::RightParen => TokenKind::RightParen.to_string(),
            Operator::As => TokenKind::As.to_string(),
        }
    }

    /// Returns the precedence of this operator. Relative operator precedence is copied from the C
    /// standard.
    pub fn precedence(&self) -> u32 {
        100 - match self {
            Operator::As => 0,
            Operator::LeftParen | Operator::RightParen => 1,
            Operator::LogicalNot => 2,
            Operator::Multiply | Operator::Divide | Operator::Modulo => 3,
            Operator::Add | Operator::Subtract => 4,
            Operator::GreaterThan
            | Operator::LessThan
            | Operator::GreaterThanOrEqual
            | Operator::LessThanOrEqual => 6,
            Operator::EqualTo | Operator::NotEqualTo | Operator::Like | Operator::NotLike => 7,
            Operator::LogicalAnd => 11,
            Operator::LogicalOr => 12,
        }
    }

    /// Returns true if the operator is left-associative. Operator associativity is copied from
    /// the C standard.
    pub fn is_left_associative(&self) -> bool {
        match self {
            Operator::LogicalNot => false,
            _ => true,
        }
    }

    /// Returns true if this is a binary operator.
    pub fn is_binary(&self) -> bool {
        match self {
            Operator::LogicalNot => false,
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
                | Operator::Like
                | Operator::NotLike
                | Operator::NotEqualTo
                | Operator::GreaterThan
                | Operator::LessThan
                | Operator::GreaterThanOrEqual
                | Operator::LessThanOrEqual
        )
    }

    /// Returns true if this operator can be used in constant expressions.
    pub fn is_const(&self) -> bool {
        matches!(
            self,
            Operator::Add
                | Operator::Subtract
                | Operator::Multiply
                | Operator::Divide
                | Operator::Modulo
                | Operator::LogicalAnd
                | Operator::LogicalOr
                | Operator::As
                | Operator::LogicalNot
                | Operator::EqualTo
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
