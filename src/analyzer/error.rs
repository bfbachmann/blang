use std::fmt;

use colored::*;

use crate::lexer::pos::{Locatable, Position};
use crate::parser::expr::Expression;
use crate::parser::statement::Statement;

pub type AnalyzeResult<T> = Result<T, AnalyzeError>;

#[derive(PartialEq, Debug, Clone)]
pub enum ErrorKind {
    IncompatibleTypes,
    ExpectedReturnValue,
    FunctionAlreadyDefined,
    TypeAlreadyDefined,
    TypeNotDefined,
    VariableNotDefined,
    StructFieldNotDefined,
    StructFieldNotInitialized,
    MemberNotDefined,
    VariableAlreadyDefined,
    DuplicateStructFieldName,
    WrongNumberOfArgs,
    UnexpectedBreak,
    UnexpectedContinue,
    UnexpectedReturn,
    CallToMain,
    MissingReturn,
    InvalidMain,
    InfiniteSizedType,
    MissingTypeName,
    UnexpectedTypeName,
    InvalidStatement,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ErrorKind::IncompatibleTypes => write!(f, "incompatible types"),
            ErrorKind::ExpectedReturnValue => write!(f, "expected return value"),
            ErrorKind::FunctionAlreadyDefined => write!(f, "function already defined"),
            ErrorKind::TypeAlreadyDefined => write!(f, "type already defined"),
            ErrorKind::TypeNotDefined => write!(f, "type not defined"),
            ErrorKind::VariableNotDefined => write!(f, "variable not defined"),
            ErrorKind::StructFieldNotDefined => write!(f, "struct field not defined"),
            ErrorKind::StructFieldNotInitialized => write!(f, "struct field not initialized"),
            ErrorKind::VariableAlreadyDefined => write!(f, "variable already defined"),
            ErrorKind::DuplicateStructFieldName => write!(f, "duplicate struct field name"),
            ErrorKind::WrongNumberOfArgs => write!(f, "wrong number of arguments"),
            ErrorKind::UnexpectedBreak => write!(f, "unexpected break"),
            ErrorKind::UnexpectedContinue => write!(f, "unexpected continue"),
            ErrorKind::UnexpectedReturn => write!(f, "unexpected return"),
            ErrorKind::CallToMain => write!(f, "call to main"),
            ErrorKind::MissingReturn => write!(f, "missing function return"),
            ErrorKind::InvalidMain => write!(f, "invalid main function"),
            ErrorKind::InfiniteSizedType => write!(f, "infinite-sized type"),
            ErrorKind::MissingTypeName => write!(f, "missing type name"),
            ErrorKind::UnexpectedTypeName => write!(f, "unexpected type name"),
            ErrorKind::MemberNotDefined => write!(f, "undefined member access"),
            ErrorKind::InvalidStatement => write!(f, "invalid statement"),
        }
    }
}

/// Represents any fatal error that occurs during program analysis.
#[derive(PartialEq, Debug, Clone)]
pub struct AnalyzeError {
    pub kind: ErrorKind,
    pub message: String,
    pub detail: Option<String>,
    pub hint: Option<String>,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl fmt::Display for AnalyzeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.kind, self.message)
    }
}

impl AnalyzeError {
    pub fn new_with_locatable(kind: ErrorKind, message: &str, loc: Box<dyn Locatable>) -> Self {
        AnalyzeError {
            kind,
            message: message.to_string(),
            detail: None,
            hint: None,
            start_pos: loc.start_pos().clone(),
            end_pos: loc.end_pos().clone(),
        }
    }

    pub fn new_from_expr(kind: ErrorKind, expr: &Expression, message: &str) -> Self {
        AnalyzeError {
            kind,
            message: message.to_string(),
            detail: Some(format!(
                "invalid expression: {}",
                format!("{}", expr).as_str().underline()
            )),
            hint: None,
            start_pos: expr.start_pos().clone(),
            end_pos: expr.end_pos().clone(),
        }
    }

    pub fn new_from_statement(kind: ErrorKind, statement: &Statement, message: &str) -> Self {
        AnalyzeError {
            kind,
            message: message.to_string(),
            detail: Some(format!(
                "invalid statement: {}",
                format!("{}", statement).as_str().underline()
            )),
            hint: None,
            start_pos: statement.start_pos().clone(),
            end_pos: statement.end_pos().clone(),
        }
    }

    pub fn with_detail(self, detail: &str) -> Self {
        AnalyzeError {
            kind: self.kind,
            message: self.message,
            detail: Some(detail.to_string()),
            hint: self.hint,
            start_pos: self.start_pos,
            end_pos: self.end_pos,
        }
    }

    pub fn with_hint(self, hint: &str) -> Self {
        AnalyzeError {
            kind: self.kind,
            message: self.message,
            detail: self.detail,
            hint: Some(hint.to_string()),
            start_pos: self.start_pos,
            end_pos: self.end_pos,
        }
    }
}
