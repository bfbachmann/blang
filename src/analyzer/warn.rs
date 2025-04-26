use crate::analyzer::ast::statement::AStatement;
use crate::lexer::pos::Span;
use std::fmt::{Display, Formatter};

/// Represents a kind of warning emitted by the semantic analyzer.
#[derive(Debug, PartialEq, Clone)]
pub enum WarnKind {
    UnreachableCode,
}

impl Display for WarnKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            WarnKind::UnreachableCode => write!(f, "unreachable code"),
        }
    }
}

/// Represents a warning issued by the semantic analyzer.
#[derive(Debug, PartialEq, Clone)]
pub struct AnalyzeWarning {
    pub kind: WarnKind,
    pub message: String,
    pub span: Span,
}

impl Display for AnalyzeWarning {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl AnalyzeWarning {
    /// Creates a new warning message with start and end positions cloned from the locatable.
    pub fn new(kind: WarnKind, message: &str, span: Span) -> AnalyzeWarning {
        AnalyzeWarning {
            kind,
            message: message.to_string(),
            span,
        }
    }
}

pub fn warn_unreachable_case(span: Span) -> AnalyzeWarning {
    AnalyzeWarning::new(WarnKind::UnreachableCode, "unreachable case", span)
}

pub fn warn_unreachable_statements(statement: &AStatement, span: Span) -> AnalyzeWarning {
    AnalyzeWarning::new(
        WarnKind::UnreachableCode,
        format_code!(
            "statements following {} will never be executed",
            match statement {
                AStatement::Continue(_) => "continue",
                AStatement::Break(_) => "break",
                AStatement::Yield(_) => "yield",
                AStatement::Return(_) => "return",
                _ => unreachable!(),
            }
        )
        .as_str(),
        span,
    )
}
