use crate::analyzer::error::AnalyzeError;

mod closure;
mod error;
mod expr;
mod func;
mod prog_context;
mod program;
mod statement;
mod var_assign;
mod var_dec;

type AnalyzeResult<T> = Result<T, AnalyzeError>;
