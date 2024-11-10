use crate::analyzer::ast::r#loop::ALoop;
use crate::codegen::error::CodeGenResult;

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
    pub(crate) fn gen_loop(&mut self, loop_: &ALoop) -> CodeGenResult<()> {
        // Create a loop context to store information about the loop.
        self.push_loop_ctx();

        let cond_block = self.get_loop_ctx().cond_block;
        let body_block = self.get_loop_ctx().body_block;

        // Generate code for the loop initialization statement, if one exists.
        if let Some(init_statement) = &loop_.maybe_init {
            let init_block = self.append_block("loop_init");
            self.builder.build_unconditional_branch(init_block);
            self.set_current_block(init_block);
            self.gen_statement(init_statement)?;

            // If the statement already jumps to some other location, there is no
            // need to continue generating code for this loop.
            if self.current_block_has_terminator() {
                return Ok(());
            }
        }

        // Jump to the conditional block for the loop. We'll use this block to generate
        // code for the loop condition that runs before each iteration.
        {
            self.builder.build_unconditional_branch(cond_block);
            self.set_current_block(cond_block);

            // If there is a loop condition, compile it and use the result to jump to the loop body block.
            // Otherwise, we'll just unconditionally jump to that block.
            match &loop_.maybe_cond {
                Some(cond_expr) => {
                    let ll_cond_val = self.gen_expr(cond_expr);
                    self.builder.build_conditional_branch(
                        ll_cond_val.into_int_value(),
                        body_block,
                        self.get_or_create_loop_end_block(),
                    );
                }
                None => {
                    self.builder.build_unconditional_branch(body_block);
                }
            };
        }

        // Generate the loop update block.
        if let Some(update_statement) = &loop_.maybe_update {
            let update_block = self.get_or_create_loop_update_block();
            self.set_current_block(update_block);
            self.gen_statement(update_statement)?;

            // Branch back to the beginning of the loop if this block doesn't already terminate.
            if !self.current_block_has_terminator() {
                self.builder.build_unconditional_branch(cond_block);
            }
        }

        // Generate code for the loop body.
        {
            self.set_current_block(body_block);
            self.gen_closure(&loop_.body)?;
        }

        // Branch back to the beginning of the loop if the body doesn't already have a terminator.
        if !self.current_block_has_terminator() {
            let begin_block = self.get_loop_begin_block();
            self.builder.build_unconditional_branch(begin_block);
        }

        // Pop the loop context now that we've compiled the loop.
        let ctx = self.pop_ctx().to_loop();

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
