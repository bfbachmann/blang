use std::collections::{HashMap, VecDeque};
use std::env::var;

use error::AnalyzeError;
use prog_context::ProgramContext;

use crate::parser::expr::Expression;
use crate::parser::op::Operator;
use crate::parser::program::Program;
use crate::parser::r#fn::Function;
use crate::parser::r#type::Type;
use crate::parser::statement::Statement;
use crate::parser::var_dec::VariableDeclaration;

mod error;
mod prog_context;

struct AnalyzedProgram {
    statements: Vec<Statement>,
}

type AnalyzeResult<T> = Result<T, AnalyzeError>;

fn analyze_program(program: Program) -> AnalyzeResult<AnalyzedProgram> {
    let mut ctx = ProgramContext::new();

    for statement in program.statements {
        analyze_statement(ctx, statement)?;
    }
}

fn analyze_statement(ctx: ProgramContext, statement: Statement) -> AnalyzeResult<Statement> {}

fn analyze_var_decl(
    ctx: ProgramContext,
    var_decl: VariableDeclaration,
) -> AnalyzeResult<VariableDeclaration> {
    // Check if the variable is already defined in the current scope.
    if ctx.var_is_defined_locally(var_decl.name.as_str()) {
        return Err(AnalyzeError::new(
            format!(
                r#"Variable "{}" already defined: {}"#,
                var_decl.name, var_decl
            )
            .as_str(),
            Some(var_decl),
        ));
    }

    // Analyze the expression assigned to the variable.

    // Check that the variable type matches the expression type.
}

fn analyze_expr(ctx: ProgramContext, expr: Expression) -> AnalyzeResult<Type> {
    match expr {
        var_ref @ Expression::VariableReference(_) => Ok(analyze_var_ref(ctx, var_ref)?),
        unary_op @ Expression::UnaryOperation(_, _) => Ok(analyze_unary_op(ctx, unary_op)?),
        _ => Err(AnalyzeError::new("Unimplemented", None)),
    }
}

fn analyze_unary_op(
    ctx: ProgramContext,
    unary_op: Expression::UnaryOperation,
) -> AnalyzeResult<Type> {
    match unary_op {
        (Operator::Not, expr) => {
            let typ = analyze_expr(ctx, expr)?;
            if let Type::Bool = typ {
                Ok(typ)
            }
            Err(AnalyzeError::new(
                format!("Expected expression of type bool, but got {}", typ).as_str(),
                expr,
            ))
        }
        (other_op, _) => Err(AnalyzeError::new(
            format!("Invalid unary operator {}", other_op).as_str(),
            other_op,
        )),
    }
}

fn analyze_var_ref(
    ctx: ProgramContext,
    var_ref: Expression::VariableReference,
) -> AnalyzeResult<Type> {
    match ctx.resolve_var_type(var_ref) {
        Some(&typ) => Ok(typ),
        None => Err(AnalyzeError::new(
            format!("Variable {} is not defined", var_ref.1).as_str(),
            var_ref,
        )),
    }
}
