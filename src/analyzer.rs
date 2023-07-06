use crate::analyzer::error::AnalyzeError;

mod closure;
mod cond;
mod error;
mod expr;
mod func;
pub mod prog_context;
pub mod program;
pub mod statement;
mod var_assign;
mod var_dec;

type AnalyzeResult<T> = Result<T, AnalyzeError>;
