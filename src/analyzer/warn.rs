use crate::analyzer::ast::statement::AStatement;
use crate::lexer::pos::Span;
use std::fmt::{Display, Formatter};

/// Represents a kind of warning emitted by the semantic analyzer.
#[derive(Debug, PartialEq, Clone)]
pub enum WarnKind {
    Unreachable,
    Unused,
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
    AnalyzeWarning::new(WarnKind::Unreachable, "unreachable case", span)
}

pub fn warn_unreachable(statement: &AStatement, span: Span) -> AnalyzeWarning {
    AnalyzeWarning::new(
        WarnKind::Unreachable,
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

pub fn warn_unused(name: &str, span: Span) -> AnalyzeWarning {
    AnalyzeWarning::new(
        WarnKind::Unused,
        format_code!("{} is unused", name).as_str(),
        span,
    )
}
