use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::AnalyzeResult;
use crate::parser::statement::Statement;
use crate::parser::var_dec::VariableDeclaration;

fn analyze_var_decl(ctx: &mut ProgramContext, var_decl: &VariableDeclaration) -> AnalyzeResult<()> {
    // Check if the variable is already defined in the current scope.
    if let Some(other_var) = ctx.get_var(var_decl.name.as_str()) {
        return Err(AnalyzeError::new_from_statement(
            ErrorKind::VariableAlreadyDefined,
            &Statement::VariableDeclaration(var_decl.clone()),
            format!(
                "Variable {} was already defined in the current scope: {}",
                var_decl.name, other_var,
            )
            .as_str(),
        ));
    }

    // Check the expression being assigned to this new variable.
    // TODO

    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::analyzer::prog_context::ProgramContext;
    use crate::analyzer::var_dec::analyze_var_decl;
    use crate::parser::expr::Expression;
    use crate::parser::r#type::Type;
    use crate::parser::var_dec::VariableDeclaration;

    #[test]
    fn var_decl() {
        let mut ctx = ProgramContext::new();
        let result = analyze_var_decl(
            &mut ctx,
            &VariableDeclaration::new(
                Type::String,
                "my_string".to_string(),
                Expression::StringLiteral("bingo".to_string()),
            ),
        );
        assert_eq!(result, Ok(()))
    }
}
