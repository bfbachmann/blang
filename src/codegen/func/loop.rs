use crate::analyzer::ast::closure::AClosure;
use crate::codegen::error::CompileResult;

use super::FnCodeGen;

impl<'a, 'ctx> FnCodeGen<'a, 'ctx> {
    /// Compiles a break statement.
    pub(crate) fn gen_break(&mut self) {
        self.set_guarantees_terminator(true);
        let loop_end = self.get_or_create_loop_end_block();
        self.builder.build_unconditional_branch(loop_end);
    }

    /// Compiles a continue statement.
    pub(crate) fn gen_continue(&mut self) {
        self.set_guarantees_terminator(true);
        let loop_begin = self.get_loop_begin_block();
        self.builder.build_unconditional_branch(loop_begin);
    }

    /// Compiles a loop.
    pub(crate) fn gen_loop(&mut self, loop_body: &AClosure) -> CompileResult<()> {
        // Create a loop context to store information about the loop body.
        self.push_loop_ctx();

        // Create a new block for the loop body, and branch to it.
        let begin_block = self.get_loop_ctx().begin_block;
        self.builder.build_unconditional_branch(begin_block);
        self.set_current_block(begin_block);

        // Compile the loop body.
        self.gen_closure(loop_body)?;

        // Pop the loop context now that we've compiled the loop body.
        let ctx = self.pop_ctx().to_loop();

        // If the loop doesn't already end in a terminator instruction, we need to branch back
        // to the beginning of the loop.
        if !ctx.guarantees_terminator {
            self.builder.build_unconditional_branch(begin_block);
        }

        // Update the parent context with return information.
        self.set_guarantees_return(ctx.guarantees_return);

        // If there is a loop end block, it means the loop has a break and we need to continue
        // compilation on the loop end block. In this case, we also inform the parent context
        // that this loop is not guaranteed to end in a terminator or return (since it can be broken
        // out of).
        if let Some(end_block) = ctx.end_block {
            self.set_current_block(end_block);
            self.set_guarantees_terminator(false);
            self.set_guarantees_return(false);
        } else {
            // The loop has no break statements.
            self.set_guarantees_terminator(true);

            // If there is a return inside the loop and it never breaks, we can tell the
            // parent context that is is guaranteed to return (or run forever, which is fine).
            self.set_guarantees_return(ctx.contains_return);
        }

        Ok(())
    }
}
