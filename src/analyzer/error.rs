use std::fmt;

use crate::lexer::pos::{Locatable, Span};

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
    UndefMod,
    StructFieldNotInitialized,
    UndefMember,
    AmbiguousAccess,
    DuplicateStructField,
    DuplicateEnumVariant,
    WrongNumberOfArgs,
    UnexpectedBreak,
    UnexpectedContinue,
    UnexpectedReturn,
    UnexpectedYield,
    MissingReturn,
    MissingYield,
    InvalidMain,
    InfiniteSizedType,
    MissingTypeName,
    UnexpectedTypeName,
    InvalidStatement,
    ImmutableAssignment,
    InvalidMutRef,
    InvalidAssignmentTarget,
    UseOfMovedValue,
    UseOfPrivateValue,
    IllegalMove,
    TypeIsNotStruct,
    TypeIsNotEnum,
    DuplicateSpec,
    UndefSpec,
    DuplicateParam,
    UnexpectedParams,
    UnresolvedParams,
    WrongNumberOfParams,
    DuplicateFnArg,
    InvalidTypeCast,
    SuperfluousTypeCast,
    InvalidExtern,
    InvalidArraySize,
    IndexOutOfBounds,
    LiteralOutOfRange,
    SpecNotSatisfied,
    SpecNotImplemented,
    ImportCycle,
    DuplicateImportName,
    IllegalImpl,
    IllegalSelfArg,
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
            ErrorKind::UndefMod => write!(f, "undefined module"),
            ErrorKind::UndefStructField => write!(f, "undefined struct field"),
            ErrorKind::StructFieldNotInitialized => write!(f, "struct field not initialized"),
            ErrorKind::DuplicateStructField => write!(f, "duplicate struct field"),
            ErrorKind::DuplicateEnumVariant => write!(f, "duplicate enum variant"),
            ErrorKind::WrongNumberOfArgs => write!(f, "wrong number of arguments"),
            ErrorKind::UnexpectedBreak => write!(f, "unexpected break"),
            ErrorKind::UnexpectedContinue => write!(f, "unexpected continue"),
            ErrorKind::UnexpectedReturn => write!(f, "unexpected return"),
            ErrorKind::UnexpectedYield => write!(f, "unexpected yield"),
            ErrorKind::MissingReturn => write!(f, "missing function return"),
            ErrorKind::MissingYield => write!(f, "missing yield"),
            ErrorKind::InvalidMain => write!(f, "invalid main function"),
            ErrorKind::InfiniteSizedType => write!(f, "infinite-sized type"),
            ErrorKind::MissingTypeName => write!(f, "missing type name"),
            ErrorKind::UnexpectedTypeName => write!(f, "unexpected type name"),
            ErrorKind::UndefMember => write!(f, "undefined member access"),
            ErrorKind::AmbiguousAccess => write!(f, "ambiguous member access"),
            ErrorKind::InvalidStatement => write!(f, "invalid statement"),
            ErrorKind::ImmutableAssignment => write!(f, "assignment to immutable value"),
            ErrorKind::InvalidMutRef => write!(f, "invalid mutable reference"),
            ErrorKind::InvalidAssignmentTarget => write!(f, "invalid assignment target"),
            ErrorKind::UseOfMovedValue => write!(f, "use of moved value"),
            ErrorKind::UseOfPrivateValue => write!(f, "use of private value"),
            ErrorKind::IllegalMove => write!(f, "illegal move"),
            ErrorKind::TypeIsNotStruct => write!(f, "type is not struct"),
            ErrorKind::TypeIsNotEnum => write!(f, "type is not enum"),
            ErrorKind::DuplicateSpec => write!(f, "duplicate spec"),
            ErrorKind::DuplicateParam => write!(f, "duplicate generic parameter"),
            ErrorKind::UnresolvedParams => write!(f, "unresolved generic parameters"),
            ErrorKind::UnexpectedParams => write!(f, "unexpected generic parameters"),
            ErrorKind::WrongNumberOfParams => write!(f, "wrong number of parameters"),
            ErrorKind::DuplicateFnArg => write!(f, "duplicate function argument"),
            ErrorKind::UndefSpec => write!(f, "undefined spec"),
            ErrorKind::InvalidTypeCast => write!(f, "invalid type cast"),
            ErrorKind::SuperfluousTypeCast => write!(f, "superfluous type cast"),
            ErrorKind::ExpectedExpr => write!(f, "expected expression"),
            ErrorKind::InvalidExtern => write!(f, "invalid extern"),
            ErrorKind::InvalidArraySize => write!(f, "invalid array size"),
            ErrorKind::IndexOutOfBounds => write!(f, "index out of bounds"),
            ErrorKind::LiteralOutOfRange => write!(f, "literal out of range"),
            ErrorKind::SpecNotSatisfied => write!(f, "unsatisfied spec"),
            ErrorKind::SpecNotImplemented => write!(f, "spec not implemented"),
            ErrorKind::ImportCycle => write!(f, "import cycle"),
            ErrorKind::DuplicateImportName => write!(f, "duplicate import name"),
            ErrorKind::IllegalImpl => write!(f, "illegal impl"),
            ErrorKind::IllegalSelfArg => write!(f, "illegal argument `self`"),
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
    pub span: Span,
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
            span: loc.span().clone(),
        }
    }

    pub fn with_detail(self, detail: &str) -> AnalyzeError {
        AnalyzeError {
            kind: self.kind,
            message: self.message,
            detail: Some(detail.to_string()),
            help: self.help,
            span: self.span,
        }
    }

    pub fn with_help(self, help: &str) -> AnalyzeError {
        AnalyzeError {
            kind: self.kind,
            message: self.message,
            detail: self.detail,
            help: Some(help.to_string()),
            span: self.span,
        }
    }
}
