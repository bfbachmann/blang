//! The Blang codegen module is responsible for generating LLVM IR from a semantically valid AST
//! that comes from the analyzer.

pub mod convert;
pub mod error;
mod func;
mod module;
pub mod program;
mod scope;
