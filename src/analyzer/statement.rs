use crate::analyzer::closure::{analyze_break, analyze_closure};
use crate::analyzer::cond::analyze_cond;
use crate::analyzer::func::analyze_fn_decl;
use crate::analyzer::func::{analyze_fn_call, analyze_return};
use crate::analyzer::prog_context::{ProgramContext, ScopeKind};
use crate::analyzer::var_assign::analyze_var_assign;
use crate::analyzer::var_dec::analyze_var_decl;
use crate::analyzer::AnalyzeResult;
use crate::parser::r#type::Type;
use crate::parser::statement::Statement;

pub fn analyze_statement(
    ctx: &mut ProgramContext,
    statement: &Statement,
) -> AnalyzeResult<Option<Type>> {
    match statement {
        Statement::VariableDeclaration(var_decl) => {
            analyze_var_decl(ctx, &var_decl)?;
        }
        Statement::VariableAssignment(var_assign) => {
            analyze_var_assign(ctx, &var_assign)?;
        }
        Statement::FunctionDeclaration(fn_decl) => {
            analyze_fn_decl(ctx, &fn_decl)?;
        }
        Statement::Closure(closure) => {
            let ret_type = analyze_closure(ctx, &closure, ScopeKind::Inline, vec![], None)?;
            return Ok(ret_type);
        }
        Statement::FunctionCall(call) => match analyze_fn_call(ctx, &call) {
            Err(e) => {
                return Err(e);
            }
            Ok(_) => {}
        },
        Statement::Conditional(cond) => {
            let ret_type = analyze_cond(ctx, cond)?;
            return Ok(ret_type);
        }
        Statement::Loop(the_loop) => {
            let ret_type = analyze_closure(ctx, &the_loop.closure, ScopeKind::Loop, vec![], None)?;
            return Ok(ret_type);
        }
        Statement::Break => {
            analyze_break(ctx)?;
        }
        Statement::Return(expr) => {
            let ret_type = analyze_return(ctx, expr)?;
            return Ok(ret_type);
        }
    };

    Ok(None)
}
