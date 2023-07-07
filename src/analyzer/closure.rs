use log::warn;

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
    expected_ret_type: Option<Type>,
) -> AnalyzeResult<Option<Type>> {
    // Add a new scope to the program context, since each closure gets its own scope.
    ctx.push_scope(Scope::new(kind, args, expected_ret_type.clone()));

    // Analyze all the statements in the closure and record return type.
    let mut ret_type = None;
    for (i, statement) in closure.statements.iter().enumerate() {
        ret_type = analyze_statement(ctx, statement)?;
        if ret_type.is_some() && i < closure.statements.len() - 1 {
            // TODO: improve warnings
            warn!("Some statements will not be executed");
        }
    }

    // Make sure the return type is as expected.
    if let Some(expected) = &expected_ret_type {
        match &ret_type {
            Some(found) => {
                if found != expected {
                    return Err(AnalyzeError::new(
                        ErrorKind::IncompatibleTypes,
                        format!("Expected return type {}, but found {}", expected, found).as_str(),
                    ));
                }
            }
            None => {
                return Err(AnalyzeError::new(
                    ErrorKind::MissingReturn,
                    format!("Expected return value of type {}", expected).as_str(),
                ));
            }
        }
    }

    // TODO: handle closure result.

    // Pop the scope from the stack before returning since we're exiting the closure scope.
    ctx.pop_scope();
    Ok(ret_type)
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
