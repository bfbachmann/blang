use crate::analyzer::closure::analyze_closure;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::analyze_expr;
use crate::analyzer::prog_context::{ProgramContext, ScopeKind};
use crate::analyzer::AnalyzeResult;
use crate::parser::cond::Conditional;
use crate::parser::r#type::Type;

pub(crate) fn analyze_cond(ctx: &mut ProgramContext, cond: &Conditional) -> AnalyzeResult<()> {
    for branch in &cond.branches {
        // Check that the branch expression evaluates to a bool, if one exists.
        if let Some(branch_cond) = &branch.condition {
            let typ = analyze_expr(ctx, branch_cond)?;
            if typ != Type::Bool {
                return Err(AnalyzeError::new(
                    ErrorKind::IncompatibleTypes,
                    format!(
                        "Expected branch condition to have type bool, but found type {}",
                        typ
                    )
                    .as_str(),
                ));
            }
        }

        // Analyze the branch body.
        analyze_closure(ctx, &branch.body, ScopeKind::Branch, vec![], None)?;
    }

    Ok(())
}
