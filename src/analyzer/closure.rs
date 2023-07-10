use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::{ProgramContext, Scope, ScopeKind};
use crate::analyzer::statement::RichStatement;
use crate::analyzer::AnalyzeResult;
use crate::parser::arg::Argument;
use crate::parser::closure::Closure;
use crate::parser::r#type::Type;
use crate::util;

#[derive(Debug)]
pub struct RichClosure {
    pub statements: Vec<RichStatement>,
    pub ret_type: Option<Type>,
}

impl fmt::Display for RichClosure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{...}}")
    }
}

impl PartialEq for RichClosure {
    fn eq(&self, other: &Self) -> bool {
        util::vectors_are_equal(&self.statements, &other.statements)
            && util::optionals_are_equal(&self.ret_type, &other.ret_type)
    }
}

impl RichClosure {
    pub fn from(
        ctx: &mut ProgramContext,
        closure: Closure,
        kind: ScopeKind,
        args: Vec<Argument>,
        expected_ret_type: Option<Type>,
    ) -> AnalyzeResult<Self> {
        // Add a new scope to the program context, since each closure gets its own scope.
        ctx.push_scope(Scope::new(kind, args, expected_ret_type.clone()));

        // Analyze all the statements in the closure and record return type.
        let mut rich_statements = vec![];
        let mut ret_type = None;
        let statement_count = closure.statements.len();
        for (i, statement) in closure.statements.into_iter().enumerate() {
            let rich_statement = RichStatement::from(ctx, statement)?;

            // If this is a return, make sure it is the last statement in the closure.
            if let RichStatement::Return(ret) = &rich_statement {
                if i + 1 == statement_count {
                    ret_type = match &ret.val {
                        Some(rich_expr) => Some(rich_expr.typ.clone()),
                        None => None,
                    };
                } else {
                    return Err(AnalyzeError::new(
                        ErrorKind::UnexpectedReturn,
                        "statements exist after unconditional return",
                    ));
                }
            }

            rich_statements.push(rich_statement);
        }

        // Make sure the return type is as expected.
        if let Some(expected) = &expected_ret_type {
            match &ret_type {
                Some(found) => {
                    if found != expected {
                        return Err(AnalyzeError::new(
                            ErrorKind::IncompatibleTypes,
                            format!("expected return type {}, but found {}", expected, found)
                                .as_str(),
                        ));
                    }
                }
                None => {
                    return Err(AnalyzeError::new(
                        ErrorKind::MissingReturn,
                        format!("expected return value of type {}", expected).as_str(),
                    ));
                }
            }
        }

        // TODO: handle closure result.

        // Pop the scope from the stack before returning since we're exiting the closure scope.
        ctx.pop_scope();
        Ok(RichClosure {
            statements: rich_statements,
            ret_type,
        })
    }
}

pub fn analyze_break(ctx: &mut ProgramContext) -> AnalyzeResult<()> {
    // Make sure we are inside a loop closure.
    if ctx.is_in_loop() {
        return Ok(());
    }

    Err(AnalyzeError::new(
        ErrorKind::UnexpectedBreak,
        "cannot break from outside a loop",
    ))
}
