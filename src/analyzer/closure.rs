use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::{ProgramContext, Scope, ScopeKind};
use crate::analyzer::statement::analyze_statement;
use crate::analyzer::AnalyzeResult;
use crate::parser::arg::Argument;
use crate::parser::closure::Closure;
use crate::parser::r#type::Type;

pub fn analyze_closure(
    ctx: &mut ProgramContext,
    closure: &Closure,
    kind: ScopeKind,
    args: Vec<Argument>,
    return_type: Option<Type>,
) -> AnalyzeResult<()> {
    // Add a new scope to the program context, since each closure gets its own scope.
    ctx.push_scope(Scope::new(kind, args, return_type));

    // Analyze all the statements in the closure.
    for statement in &closure.statements {
        analyze_statement(ctx, statement)?;
    }

    // TODO: handle closure result.

    // Pop the scope from the stack before returning since we're exiting the closure scope.
    ctx.pop_scope();
    Ok(())
}

pub fn analyze_break(ctx: &mut ProgramContext) -> AnalyzeResult<()> {
    // Make sure we are inside a loop closure.
    if ctx.is_in_loop() {
        return Ok(());
    }

    Err(AnalyzeError::new(
        ErrorKind::UnexpectedBreak,
        "Cannot break from outside a loop",
    ))
}
