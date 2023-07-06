use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::analyze_expr;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::AnalyzeResult;
use crate::parser::statement::Statement;
use crate::parser::var_dec::VariableDeclaration;

pub fn analyze_var_decl(
    ctx: &mut ProgramContext,
    var_decl: &VariableDeclaration,
) -> AnalyzeResult<()> {
    // Check if the variable is already defined in this scope.
    if let Some(_) = ctx.get_var(var_decl.name.as_str()) {
        return Err(AnalyzeError::new_from_statement(
            ErrorKind::VariableAlreadyDefined,
            &Statement::VariableDeclaration(var_decl.clone()),
            format!(
                "Variable {} was already defined in this scope",
                var_decl.name,
            )
            .as_str(),
        ));
    }

    // Check the expression being assigned to this new variable.
    let expr_type = analyze_expr(ctx, &var_decl.value)?;
    if expr_type != var_decl.typ {
        return Err(AnalyzeError::new_from_statement(
            ErrorKind::IncompatibleTypes,
            &Statement::VariableDeclaration(var_decl.clone()),
            format!(
                "Cannot assign value of type {} to variable {} of type {}",
                expr_type, var_decl.name, var_decl.typ
            )
            .as_str(),
        ));
    }

    // The variable expression is valid. Add it to the program context.
    ctx.add_var(var_decl.clone());
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::analyzer::error::{AnalyzeError, ErrorKind};
    use crate::analyzer::prog_context::ProgramContext;
    use crate::analyzer::var_dec::analyze_var_decl;
    use crate::parser::expr::Expression;
    use crate::parser::r#type::Type;
    use crate::parser::var_dec::VariableDeclaration;

    #[test]
    fn var_already_defined() {
        let mut ctx = ProgramContext::new();
        let var_decl = &VariableDeclaration::new(
            Type::String,
            "my_string".to_string(),
            Expression::StringLiteral("bingo".to_string()),
        );
        let result = analyze_var_decl(&mut ctx, var_decl);
        assert_eq!(result, Ok(()));

        let result = analyze_var_decl(&mut ctx, var_decl);
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::VariableAlreadyDefined,
                ..
            })
        ));
    }

    #[test]
    fn type_mismatch() {
        let mut ctx = ProgramContext::new();
        let var_decl = &VariableDeclaration::new(
            Type::I64,
            "my_string".to_string(),
            Expression::StringLiteral("bingo".to_string()),
        );
        let result = analyze_var_decl(&mut ctx, var_decl);
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::IncompatibleTypes,
                ..
            })
        ));
    }
}
