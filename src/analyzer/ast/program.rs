use crate::analyzer::ast::statement::AStatement;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::parser::program::Program;
use crate::parser::statement::Statement;

/// Represents a semantically valid and type-rich program.
#[derive(Debug)]
pub struct AProgram {
    pub statements: Vec<AStatement>,
}

impl AProgram {
    /// Performs semantic analysis on the given program and returns a type-rich version of it.
    pub fn from(ctx: &mut ProgramContext, prog: &Program) -> Self {
        let mut analyzed_statements = vec![];

        // Analyze each statement in the program.
        for statement in &prog.statements {
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
                    // `Program::define_fns`.
                }

                other => {
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::InvalidStatement,
                        "expected type, constant, spec, or function declaration",
                        other,
                    ));
                }
            }
        }

        AProgram {
            statements: analyzed_statements,
        }
    }
}
