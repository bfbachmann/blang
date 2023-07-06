use crate::analyzer::closure::{analyze_break, analyze_closure};
use crate::analyzer::cond::analyze_cond;
use crate::analyzer::func::analyze_fn_decl;
use crate::analyzer::func::{analyze_fn_call, analyze_return};
use crate::analyzer::prog_context::{ProgramContext, ScopeKind};
use crate::analyzer::var_assign::analyze_var_assign;
use crate::analyzer::var_dec::analyze_var_decl;
use crate::analyzer::AnalyzeResult;
use crate::parser::statement::Statement;

pub fn analyze_statement(ctx: &mut ProgramContext, statement: &Statement) -> AnalyzeResult<()> {
    match statement {
        Statement::VariableDeclaration(var_decl) => analyze_var_decl(ctx, &var_decl),
        Statement::VariableAssignment(var_assign) => analyze_var_assign(ctx, &var_assign),
        Statement::FunctionDeclaration(fn_decl) => analyze_fn_decl(ctx, &fn_decl),
        Statement::Closure(closure) => {
            analyze_closure(ctx, &closure, ScopeKind::Inline, vec![], None)
        }
        Statement::FunctionCall(call) => match analyze_fn_call(ctx, &call) {
            Err(e) => Err(e),
            Ok(_) => Ok(()),
        },
        Statement::Conditional(cond) => analyze_cond(ctx, cond),
        Statement::Loop(the_loop) => {
            analyze_closure(ctx, &the_loop.closure, ScopeKind::Loop, vec![], None)
        }
        Statement::Break => analyze_break(ctx),
        Statement::Return(expr) => analyze_return(ctx, expr),
    }
}
