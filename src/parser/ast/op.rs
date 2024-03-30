use core::fmt;

use crate::lexer::token_kind::TokenKind;

/// Represents an operator.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
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
    Reference,
    MutReference,
    Defererence,

    // Comparators
    EqualTo,
    Like,
    NotLike,
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
    /// Creates an operator from the given token kind. Returns `None` if the kind is not a valid
    /// operator.
    pub fn from(kind: &TokenKind) -> Option<Self> {
        match kind {
            TokenKind::Plus => Some(Operator::Add),
            TokenKind::Minus => Some(Operator::Subtract),
            TokenKind::Asterisk => Some(Operator::Multiply),
            TokenKind::ForwardSlash => Some(Operator::Divide),
            TokenKind::Percent => Some(Operator::Modulo),
            TokenKind::LogicalAnd => Some(Operator::LogicalAnd),
            TokenKind::LogicalOr => Some(Operator::LogicalOr),
            TokenKind::LogicalNot => Some(Operator::LogicalNot),
            TokenKind::EqualTo => Some(Operator::EqualTo),
            TokenKind::NotEqualTo => Some(Operator::NotEqualTo),
            TokenKind::GreaterThan => Some(Operator::GreaterThan),
            TokenKind::LessThan => Some(Operator::LessThan),
            TokenKind::GreaterThanOrEqual => Some(Operator::GreaterThanOrEqual),
            TokenKind::LessThanOrEqual => Some(Operator::LessThanOrEqual),
            TokenKind::As => Some(Operator::As),
            TokenKind::Like => Some(Operator::Like),
            TokenKind::NotLike => Some(Operator::NotLike),
            TokenKind::Ref => Some(Operator::Reference),
            TokenKind::RefMut => Some(Operator::MutReference),
            TokenKind::Deref => Some(Operator::Defererence),
            _ => None,
        }
    }

    pub fn to_string(&self) -> String {
        match self {
            Operator::Add => TokenKind::Plus.to_string(),
            Operator::Subtract => TokenKind::Minus.to_string(),
            Operator::Multiply => TokenKind::Asterisk.to_string(),
            Operator::Divide => TokenKind::ForwardSlash.to_string(),
            Operator::Modulo => TokenKind::Percent.to_string(),
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
            Operator::As => TokenKind::As.to_string(),
            Operator::Reference => TokenKind::Ref.to_string(),
            Operator::MutReference => TokenKind::RefMut.to_string(),
            Operator::Defererence => TokenKind::Deref.to_string(),
        }
    }

    /// Returns the precedence of this operator. Relative operator precedence is copied from the C
    /// standard.
    pub fn precedence(&self) -> u32 {
        100 - match self {
            Operator::LogicalNot
            | Operator::Reference
            | Operator::MutReference
            | Operator::Defererence => 2,

            Operator::As => 3,

            Operator::Multiply | Operator::Divide | Operator::Modulo => 4,

            Operator::Add | Operator::Subtract => 5,

            Operator::GreaterThan
            | Operator::LessThan
            | Operator::GreaterThanOrEqual
            | Operator::LessThanOrEqual => 6,

            Operator::EqualTo | Operator::NotEqualTo | Operator::Like | Operator::NotLike => 7,

            Operator::LogicalAnd => 8,

            Operator::LogicalOr => 9,
        }
    }

    /// Returns true if the operator is left-associative. Operator associativity is copied from
    /// the C standard.
    pub fn is_left_associative(&self) -> bool {
        match self {
            Operator::LogicalNot
            | Operator::Reference
            | Operator::MutReference
            | Operator::Defererence => false,
            _ => true,
        }
    }

    /// Returns true if this is a binary operator.
    pub fn is_binary(&self) -> bool {
        match self {
            Operator::LogicalNot
            | Operator::Reference
            | Operator::MutReference
            | Operator::Defererence => false,
            _ => true,
        }
    }

    /// Returns true if this is a unary operator. Note that some operators like subtract
    /// can be both binary and unary.
    pub fn is_unary(&self) -> bool {
        !self.is_binary() || self == &Operator::Subtract
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

    /// Returns true if the operator is a binary logical operator.
    pub fn is_logical(&self) -> bool {
        matches!(self, Operator::LogicalAnd | Operator::LogicalOr)
    }
}
