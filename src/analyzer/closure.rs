use crate::analyzer::prog_context::{ProgramContext, Scope};
use crate::analyzer::statement::analyze_statement;
use crate::analyzer::AnalyzeResult;
use crate::parser::closure::Closure;

pub fn analyze_closure(ctx: &mut ProgramContext, closure: &Closure) -> AnalyzeResult<()> {
    // Add a new scope to the program context, since each closure gets its own scope.
    let scope = Scope::new();
    ctx.push_scope(scope);

    // Analyze all the statements in the closure.
    for statement in &closure.statements {
        analyze_statement(ctx, statement)?;
    }

    // TODO: handle closure result.

    // Pop the scope from the stack before returning since we're exiting the closure scope.
    ctx.pop_scope();
    Ok(())
}
