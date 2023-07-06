use crate::analyzer::closure::analyze_closure;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func::analyze_fn_call;
use crate::analyzer::func::analyze_fn_decl;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::var_assign::analyze_var_assign;
use crate::analyzer::var_dec::analyze_var_decl;
use crate::analyzer::AnalyzeResult;
use crate::parser::statement::Statement;

pub fn analyze_statement(ctx: &mut ProgramContext, statement: &Statement) -> AnalyzeResult<()> {
    match statement {
        Statement::VariableDeclaration(var_decl) => analyze_var_decl(ctx, &var_decl),
        Statement::VariableAssignment(var_assign) => analyze_var_assign(ctx, &var_assign),
        Statement::FunctionDeclaration(fn_decl) => analyze_fn_decl(ctx, &fn_decl),
        Statement::Closure(closure) => analyze_closure(ctx, &closure),
        Statement::FunctionCall(call) => match analyze_fn_call(ctx, &call) {
            Err(e) => Err(e),
            Ok(_) => Ok(()),
        },
        Statement::Conditional(_)
        | Statement::Loop(_)
        | Statement::Break
        | Statement::Return(_) => Err(AnalyzeError::new(
            ErrorKind::VariableNotDefined,
            "UNIMPLEMENTED",
        )),
    }
}
