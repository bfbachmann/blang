use std::fmt;

use crate::parser::expr::Expression;
use crate::parser::statement::Statement;

#[derive(PartialEq, Debug)]
pub enum ErrorKind {
    IncompatibleTypes,
    ExpectedValue,
    FunctionNotDefined,
    FunctionAlreadyDefined,
    VariableNotDefined,
    VariableAlreadyDefined,
    WrongNumberOfArgs,
    UnexpectedBreak,
    UnexpectedReturn,
    MissingMain,
    MissingReturn,
    InvalidMain,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ErrorKind::IncompatibleTypes => write!(f, "Incompatible types"),
            ErrorKind::ExpectedValue => write!(f, "Expected value"),
            ErrorKind::FunctionNotDefined => write!(f, "Function not defined"),
            ErrorKind::FunctionAlreadyDefined => write!(f, "Function already defined"),
            ErrorKind::VariableNotDefined => write!(f, "Variable not defined"),
            ErrorKind::VariableAlreadyDefined => write!(f, "Variable already defined"),
            ErrorKind::WrongNumberOfArgs => write!(f, "Wrong number of arguments"),
            ErrorKind::UnexpectedBreak => write!(f, "Unexpected break"),
            ErrorKind::UnexpectedReturn => write!(f, "Unexpected return"),
            ErrorKind::MissingMain => write!(f, "Missing main"),
            ErrorKind::MissingReturn => write!(f, "Missing return"),
            ErrorKind::InvalidMain => write!(f, "Invalid main"),
        }
    }
}

/// Represents any fatal error that occurs during program analysis.
#[derive(PartialEq, Debug)]
pub struct AnalyzeError {
    pub kind: ErrorKind,
    pub message: String,
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
        }
    }

    pub fn new_from_expr(kind: ErrorKind, expr: &Expression, message: &str) -> Self {
        AnalyzeError {
            kind,
            message: format!("Invalid expression {}: {}", expr, message),
        }
    }

    pub fn new_from_statement(kind: ErrorKind, statement: &Statement, message: &str) -> Self {
        AnalyzeError {
            kind,
            message: format!("Invalid statement {}: {}", statement, message),
        }
    }
}
