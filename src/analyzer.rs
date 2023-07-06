use std::collections::{HashMap, VecDeque};
use std::env::var;
use std::fmt;

use prog_context::ProgramContext;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::parser::expr::Expression;
use crate::parser::op::Operator;
use crate::parser::program::Program;
use crate::parser::r#fn::Function;
use crate::parser::r#type::Type;
use crate::parser::statement::Statement;
use crate::parser::var_dec::VariableDeclaration;

mod error;
mod expr;
mod prog_context;
mod var_dec;

struct AnalyzedProgram {
    statements: Vec<Statement>,
}

type AnalyzeResult<T> = Result<T, AnalyzeError>;

// fn analyze_program(program: Program) -> AnalyzeResult<()> {
//     let mut ctx = ProgramContext::new();
//
//     for statement in program.statements {
//         analyze_statement(&mut ctx, statement)?;
//     }
//
//     Ok(())
// }

// fn analyze_statement(ctx: &mut ProgramContext, statement: Statement) -> AnalyzeResult<()> {
//     match statement {
//         Statement::VariableDeclaration(_) => {}
//         Statement::VariableAssignment(_)
//         | Statement::FunctionDeclaration(_)
//         | Statement::Closure(_)
//         | Statement::FunctionCall(_)
//         | Statement::Conditional(_)
//         | Statement::Loop(Loop)
//         | Statement::Break
//         | Statement::Return(_) => Err(AnalyzeError::new(
//             ErrorKind::VariableNotDefined,
//             "UNIMPLEMENTED",
//             None,
//         )),
//     }
//
//     Ok(())
// }
//
// fn analyze_var_decl(ctx: &mut ProgramContext, var_decl: VariableDeclaration) -> AnalyzeResult<()> {
//     // Check if the variable is already defined in the current scope.
//     match ctx.get_local_var(var_decl.name.as_str()) {
//         Some(_) =>
//     }
//
//     // Analyze the expression assigned to the variable.
//
//     // Check that the variable type matches the expression type.
//
//     Ok(())
// }
