use std::fmt;

use crate::lexer::pos::{Locatable, Position};

pub type AnalyzeResult<T> = Result<T, AnalyzeError>;

#[derive(PartialEq, Debug, Clone)]
pub enum ErrorKind {
    MismatchedTypes,
    ExpectedReturnValue,
    FunctionAlreadyDefined,
    ConstAlreadyDefined,
    InvalidConst,
    TypeAlreadyDefined,
    TypeNotDefined,
    SymbolNotDefined,
    StructFieldNotDefined,
    StructFieldNotInitialized,
    MemberNotDefined,
    DuplicateStructField,
    DuplicateEnumVariant,
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
    ImmutableAssignment,
    UseOfMovedValue,
    TypeIsNotEnum,
    SpecAlreadyDefined,
    SpecNotDefined,
    DuplicateTmplParam,
    UnresolvedTmplParams,
    DuplicateFnArg,
    SpecNotSatisfied,
    InvalidTypeCast,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ErrorKind::MismatchedTypes => write!(f, "mismatched types"),
            ErrorKind::ExpectedReturnValue => write!(f, "expected return value"),
            ErrorKind::FunctionAlreadyDefined => write!(f, "function already defined"),
            ErrorKind::ConstAlreadyDefined => write!(f, "const already defined"),
            ErrorKind::InvalidConst => write!(f, "invalid constant declaration"),
            ErrorKind::TypeAlreadyDefined => write!(f, "type already defined"),
            ErrorKind::TypeNotDefined => write!(f, "type not defined"),
            ErrorKind::SymbolNotDefined => write!(f, "symbol not defined"),
            ErrorKind::StructFieldNotDefined => write!(f, "struct field not defined"),
            ErrorKind::StructFieldNotInitialized => write!(f, "struct field not initialized"),
            ErrorKind::DuplicateStructField => write!(f, "duplicate struct field"),
            ErrorKind::DuplicateEnumVariant => write!(f, "duplicate enum variant"),
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
            ErrorKind::ImmutableAssignment => write!(f, "assignment to immutable value"),
            ErrorKind::UseOfMovedValue => write!(f, "use of moved value"),
            ErrorKind::TypeIsNotEnum => write!(f, "type is not enum"),
            ErrorKind::SpecAlreadyDefined => write!(f, "spec already defined"),
            ErrorKind::DuplicateTmplParam => write!(f, "duplicate template parameter"),
            ErrorKind::UnresolvedTmplParams => write!(f, "unresolved template parameters"),
            ErrorKind::DuplicateFnArg => write!(f, "duplicate function argument"),
            ErrorKind::SpecNotDefined => write!(f, "spec not defined"),
            ErrorKind::SpecNotSatisfied => write!(f, "spec not satisfied"),
            ErrorKind::InvalidTypeCast => write!(f, "invalid type cast"),
        }
    }
}

/// Represents any fatal error that occurs during program analysis.
#[derive(PartialEq, Debug, Clone)]
pub struct AnalyzeError {
    pub kind: ErrorKind,
    pub message: String,
    pub detail: Option<String>,
    pub help: Option<String>,
    pub start_pos: Position,
    pub end_pos: Position,
}

impl fmt::Display for AnalyzeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.kind, self.message)
    }
}

impl AnalyzeError {
    pub fn new<T: Locatable>(kind: ErrorKind, message: &str, loc: &T) -> Self {
        AnalyzeError {
            kind,
            message: message.to_string(),
            detail: None,
            help: None,
            start_pos: loc.start_pos().clone(),
            end_pos: loc.end_pos().clone(),
        }
    }

    pub fn with_detail(self, detail: &str) -> Self {
        AnalyzeError {
            kind: self.kind,
            message: self.message,
            detail: Some(detail.to_string()),
            help: self.help,
            start_pos: self.start_pos,
            end_pos: self.end_pos,
        }
    }

    pub fn with_help(self, help: &str) -> Self {
        AnalyzeError {
            kind: self.kind,
            message: self.message,
            detail: self.detail,
            help: Some(help.to_string()),
            start_pos: self.start_pos,
            end_pos: self.end_pos,
        }
    }
}
