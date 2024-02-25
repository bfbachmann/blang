use crate::analyzer::ast::statement::AStatement;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::parser::ast::statement::Statement;
use crate::parser::module::Module;

/// Represents a semantically analyzed source file.
#[derive(Debug)]
pub struct AModule {
    pub path: String,
    pub statements: Vec<AStatement>,
}

impl AModule {
    /// Performs semantic analysis on the given module and returns a type-rich version of it.
    pub fn from(ctx: &mut ProgramContext, module: &Module) -> Self {
        let mut analyzed_statements = vec![];

        // Analyze each statement in the source file.
        for statement in &module.statements {
            match statement {
                Statement::FunctionDeclaration(_)
                | Statement::ExternFns(_)
                | Statement::Consts(_)
                | Statement::StructDeclaration(_)
                | Statement::EnumDeclaration(_)
                | Statement::Impl(_) => {
                    // Only include the statement in the output AST if it's not templated.
                    let statement = AStatement::from(ctx, &statement);
                    if !statement.is_templated() {
                        analyzed_statements.push(statement);
                    }
                }

                Statement::SpecDeclaration(_) => {
                    // We can safely skip specs here because they'll be full analyzed in
                    // `define_fns`.
                }

                Statement::Use(_) => {
                    // We can skip `use` statements since they're handled by the parser.
                }

                other => {
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::InvalidStatement,
                        "expected use, type, constant, spec, or function declaration",
                        other,
                    ));
                }
            }
        }

        AModule {
            path: module.path.clone(),
            statements: analyzed_statements,
        }
    }
}
