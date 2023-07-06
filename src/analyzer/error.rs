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
}

/// Represents any fatal error that occurs during program analysis.
#[derive(PartialEq, Debug)]
pub struct AnalyzeError {
    pub kind: ErrorKind,
    pub message: String,
}

impl fmt::Display for AnalyzeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.message)
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
