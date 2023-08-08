use std::fmt;

use crate::parser::expr::Expression;
use crate::parser::statement::Statement;

#[derive(PartialEq, Debug)]
pub enum ErrorKind {
    IncompatibleTypes,
    ExpectedValue,
    FunctionNotDefined,
    FunctionAlreadyDefined,
    TypeAlreadyDefined,
    TypeNotDefined,
    VariableNotDefined,
    StructFieldNotDefined,
    StructFieldNotInitialized,
    VariableAlreadyDefined,
    DuplicateStructFieldName,
    WrongNumberOfArgs,
    UnexpectedBreak,
    UnexpectedContinue,
    UnexpectedReturn,
    MissingMain,
    CallToMain,
    MissingReturn,
    InvalidMain,
    ContainmentCycle,
    MissingTypeName,
    UnexpectedTypeName,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ErrorKind::IncompatibleTypes => write!(f, "incompatible types"),
            ErrorKind::ExpectedValue => write!(f, "expected value"),
            ErrorKind::FunctionNotDefined => write!(f, "function not defined"),
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
            ErrorKind::MissingMain => write!(f, "missing main"),
            ErrorKind::CallToMain => write!(f, "call to main"),
            ErrorKind::MissingReturn => write!(f, "missing return"),
            ErrorKind::InvalidMain => write!(f, "invalid main"),
            ErrorKind::ContainmentCycle => write!(f, "containment cycle"),
            ErrorKind::MissingTypeName => write!(f, "missing type name"),
            ErrorKind::UnexpectedTypeName => write!(f, "unexpected type name"),
        }
    }
}

/// Represents any fatal error that occurs during program analysis.
#[derive(PartialEq, Debug)]
pub struct AnalyzeError {
    pub kind: ErrorKind,
    pub message: String,
    pub detail: Option<String>,
}

impl fmt::Display for AnalyzeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.kind, self.message)
    }
}

impl AnalyzeError {
    pub fn new(kind: ErrorKind, message: &str) -> Self {
        AnalyzeError {
            kind,
            message: message.to_string(),
            detail: None,
        }
    }

    pub fn new_from_expr(kind: ErrorKind, expr: &Expression, message: &str) -> Self {
        AnalyzeError {
            kind,
            message: message.to_string(),
            detail: Some(format!("{}", expr)),
        }
    }

    pub fn new_from_statement(kind: ErrorKind, statement: &Statement, message: &str) -> Self {
        AnalyzeError {
            kind,
            message: message.to_string(),
            detail: Some(format!("{}", statement)),
        }
    }
}
