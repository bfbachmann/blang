//! The Blang parser attempts to assemble an AST from the sequence of tokens that the lexer
//! produces.

use r#type::Type;

pub mod arg;
pub mod bool_lit;
pub mod branch;
pub mod r#break;
pub mod closure;
pub mod cond;
pub mod r#const;
pub mod cont;
pub mod r#enum;
pub mod error;
pub mod expr;
pub mod ext;
pub mod func;
pub mod func_call;
pub mod func_sig;
pub mod i64_lit;
pub mod r#impl;
pub mod lambda;
pub mod r#loop;
pub mod member;
pub mod op;
pub mod pointer;
pub mod program;
pub mod ret;
pub mod sizeof;
pub mod spec;
pub mod statement;
pub mod str_lit;
pub mod r#struct;
pub mod symbol;
mod tests;
pub mod tmpl_params;
pub mod tuple;
pub mod r#type;
pub mod u64_lit;
pub mod unresolved;
pub mod var_assign;
pub mod var_dec;
