use super::FnCodeGen;
use crate::analyzer::ast::closure::AClosure;
use crate::codegen::error::CodeGenResult;
use crate::codegen::scope::CodegenScope;

impl<'a, 'ctx> FnCodeGen<'a, 'ctx> {
    /// Compiles all statements in the closure.
    pub(crate) fn gen_closure(&mut self, closure: &AClosure) -> CodeGenResult<()> {
        self.set_di_location(&closure.span.start_pos);

        self.push_scope(CodegenScope::new_closure());

        for (i, statement) in closure.statements.iter().enumerate() {
            self.push_scope(CodegenScope::new_statement());
            self.gen_statement(statement)?;
            let statement_scope = self.pop_scope().into_statement();

            // If this is the last statement in the closure or the statement is guaranteed to end
            // in a terminator (unconditional jump) instruction, we need to propagate information
            // about terminators and returns to the parent scope.
            if i + 1 == closure.statements.len() || statement_scope.guarantees_terminator {
                self.set_guarantees_return(statement_scope.guarantees_return);
                self.set_guarantees_terminator(statement_scope.guarantees_terminator);
                break;
            }
        }

        self.pop_scope();

        Ok(())
    }
}
