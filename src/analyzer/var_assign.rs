use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::analyze_expr;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::AnalyzeResult;
use crate::parser::var_assign::VariableAssignment;

pub fn analyze_var_assign(
    ctx: &mut ProgramContext,
    assign: &VariableAssignment,
) -> AnalyzeResult<()> {
    // Analyze the expression representing the value assigned to the variable.
    let expr_type = analyze_expr(ctx, &assign.value)?;

    // Make sure the variable has been defined.
    let decl = ctx.get_var(assign.name.as_str());
    if let None = decl {
        return Err(AnalyzeError::new(
            ErrorKind::VariableNotDefined,
            format!("Cannot assign to undeclared variable {}", assign.name).as_str(),
        ));
    }

    // Make sure the variable type is the same as the expression type.
    let decl = decl.unwrap();
    if decl.typ != expr_type {
        return Err(AnalyzeError::new(
            ErrorKind::IncompatibleTypes,
            format!(
                "Cannot assign value of type {} to variable {} of type {}",
                expr_type, assign.name, decl.typ
            )
            .as_str(),
        ));
    }

    Ok(())
}
