use std::fmt;

use crate::lexer::pos::{Locatable, Position};

pub type AnalyzeResult<T> = Result<T, AnalyzeError>;

#[derive(PartialEq, Debug, Clone)]
pub enum ErrorKind {
    MismatchedTypes,
    ExpectedReturnValue,
    ExpectedExpr,
    DuplicateFunction,
    DuplicateConst,
    InvalidConst,
    DuplicateType,
    UndefType,
    UndefSymbol,
    UndefStructField,
    StructFieldNotInitialized,
    UndefMember,
    DuplicateStructField,
    DuplicateEnumVariant,
    WrongNumberOfArgs,
    UnexpectedBreak,
    UnexpectedContinue,
    UnexpectedReturn,
    MissingReturn,
    InvalidMain,
    InfiniteSizedType,
    MissingTypeName,
    UnexpectedTypeName,
    InvalidStatement,
    ImmutableAssignment,
    InvalidMutRef,
    InvalidAssignmentTarget,
    UseOfMovedValue,
    IllegalMove,
    TypeIsNotEnum,
    DuplicateSpec,
    UndefSpec,
    DuplicateTmplParam,
    UnresolvedTmplParams,
    DuplicateFnArg,
    InvalidTypeCast,
    InvalidExtern,
    InvalidArraySize,
    IndexOutOfBounds,
    #[cfg(test)]
    #[cfg(feature = "generics")]
    SpecNotSatisfied,
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ErrorKind::MismatchedTypes => write!(f, "mismatched types"),
            ErrorKind::ExpectedReturnValue => write!(f, "expected return value"),
            ErrorKind::DuplicateFunction => write!(f, "duplicate function"),
            ErrorKind::DuplicateConst => write!(f, "duplicate constant"),
            ErrorKind::InvalidConst => write!(f, "invalid constant declaration"),
            ErrorKind::DuplicateType => write!(f, "duplicate type"),
            ErrorKind::UndefType => write!(f, "undefined type"),
            ErrorKind::UndefSymbol => write!(f, "undefined symbol"),
            ErrorKind::UndefStructField => write!(f, "undefined struct field"),
            ErrorKind::StructFieldNotInitialized => write!(f, "struct field not initialized"),
            ErrorKind::DuplicateStructField => write!(f, "duplicate struct field"),
            ErrorKind::DuplicateEnumVariant => write!(f, "duplicate enum variant"),
            ErrorKind::WrongNumberOfArgs => write!(f, "wrong number of arguments"),
            ErrorKind::UnexpectedBreak => write!(f, "unexpected break"),
            ErrorKind::UnexpectedContinue => write!(f, "unexpected continue"),
            ErrorKind::UnexpectedReturn => write!(f, "unexpected return"),
            ErrorKind::MissingReturn => write!(f, "missing function return"),
            ErrorKind::InvalidMain => write!(f, "invalid main function"),
            ErrorKind::InfiniteSizedType => write!(f, "infinite-sized type"),
            ErrorKind::MissingTypeName => write!(f, "missing type name"),
            ErrorKind::UnexpectedTypeName => write!(f, "unexpected type name"),
            ErrorKind::UndefMember => write!(f, "undefined member access"),
            ErrorKind::InvalidStatement => write!(f, "invalid statement"),
            ErrorKind::ImmutableAssignment => write!(f, "assignment to immutable value"),
            ErrorKind::InvalidMutRef => write!(f, "invalid mutable reference"),
            ErrorKind::InvalidAssignmentTarget => write!(f, "invalid assignment target"),
            ErrorKind::UseOfMovedValue => write!(f, "use of moved value"),
            ErrorKind::IllegalMove => write!(f, "illegal move"),
            ErrorKind::TypeIsNotEnum => write!(f, "type is not enum"),
            ErrorKind::DuplicateSpec => write!(f, "duplicate spec"),
            ErrorKind::DuplicateTmplParam => write!(f, "duplicate template parameter"),
            ErrorKind::UnresolvedTmplParams => write!(f, "unresolved template parameters"),
            ErrorKind::DuplicateFnArg => write!(f, "duplicate function argument"),
            ErrorKind::UndefSpec => write!(f, "undefined spec"),
            ErrorKind::InvalidTypeCast => write!(f, "invalid type cast"),
            ErrorKind::ExpectedExpr => write!(f, "expected expression"),
            ErrorKind::InvalidExtern => write!(f, "invalid extern"),
            ErrorKind::InvalidArraySize => write!(f, "invalid array size"),
            ErrorKind::IndexOutOfBounds => write!(f, "index out of bounds"),
            #[cfg(test)]
            #[cfg(feature = "generics")]
            ErrorKind::SpecNotSatisfied => write!(f, "unsatisfied spec"),
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
        write!(f, "{}", self.message)
    }
}

impl AnalyzeError {
    pub fn new<T: Locatable>(kind: ErrorKind, message: &str, loc: &T) -> AnalyzeError {
        AnalyzeError {
            kind,
            message: message.to_string(),
            detail: None,
            help: None,
            start_pos: loc.start_pos().clone(),
            end_pos: loc.end_pos().clone(),
        }
    }

    pub fn with_detail(self, detail: &str) -> AnalyzeError {
        AnalyzeError {
            kind: self.kind,
            message: self.message,
            detail: Some(detail.to_string()),
            help: self.help,
            start_pos: self.start_pos,
            end_pos: self.end_pos,
        }
    }

    pub fn with_help(self, help: &str) -> AnalyzeError {
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
