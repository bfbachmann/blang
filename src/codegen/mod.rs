//! The Blang codegen module is responsible for generating LLVM IR from a semantically valid AST
//! that comes from the analyzer.

mod context;
mod convert;
pub mod error;
mod func;
pub mod program;
mod tests;
