use crate::analyzer::error::AnalyzeError;

pub mod closure;
pub mod cond;
mod error;
pub mod expr;
pub mod func;
pub mod prog_context;
pub mod program;
pub mod statement;
pub mod var_assign;
pub mod var_dec;

type AnalyzeResult<T> = Result<T, AnalyzeError>;
