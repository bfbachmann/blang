use std::fmt::{Display, Formatter};

use crate::lexer::pos::{Locatable, Position};

/// Represents a kind of warning emitted by the semantic analyzer.
#[derive(Debug, PartialEq, Clone)]
pub enum WarnKind {
    MissingMain,
    UnreachableCode,
}

impl Display for WarnKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            WarnKind::MissingMain => write!(f, "missing main"),
            WarnKind::UnreachableCode => write!(f, "unreachable code"),
        }
    }
}

/// Represents a warning issued by the semantic analyzer.
#[derive(Debug, PartialEq, Clone)]
pub struct AnalyzeWarning {
    pub kind: WarnKind,
    pub message: String,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl Display for AnalyzeWarning {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl AnalyzeWarning {
    /// Creates a new warning with default start and end positions.
    pub fn new_with_default_pos(kind: WarnKind, message: &str) -> Self {
        AnalyzeWarning {
            kind,
            message: message.to_string(),
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Creates a new warning message with start and end positions cloned from the locatable.
    pub fn new<T: Locatable>(kind: WarnKind, message: &str, loc: &T) -> AnalyzeWarning {
        AnalyzeWarning {
            kind,
            message: message.to_string(),
            start_pos: loc.start_pos().clone(),
            end_pos: loc.end_pos().clone(),
        }
    }
}
