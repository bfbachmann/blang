use crate::analyzer::ast::closure::AClosure;
use crate::codegen::error::CompileResult;

use super::FnCodeGen;

impl<'a, 'ctx> FnCodeGen<'a, 'ctx> {
    /// Compiles all statements in the closure.
    pub(crate) fn gen_closure(&mut self, closure: &AClosure) -> CompileResult<()> {
        for (i, statement) in closure.statements.iter().enumerate() {
            // Create a new statement context that can store information about the statement
            // we're about to compile.
            self.push_statement_ctx();

            self.gen_statement(statement)?;

            // Pop the statement context now that we've compiled the statement.
            let ctx = self.pop_ctx().to_statement();

            // If this is the last statement in the closure or the statement is guaranteed to end
            // in a terminator (unconditional jump) instruction, we need to propagate information
            // about terminators and returns to the parent context.
            if i + 1 == closure.statements.len() || ctx.guarantees_terminator {
                self.set_guarantees_return(ctx.guarantees_return);
                self.set_guarantees_terminator(ctx.guarantees_terminator);
                break;
            }
        }

        Ok(())
    }
}
