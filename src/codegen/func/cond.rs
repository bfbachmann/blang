use crate::analyzer::ast::cond::ACond;
use crate::codegen::error::CompileResult;

use super::FnCodeGen;

impl<'a, 'ctx> FnCodeGen<'a, 'ctx> {
    /// Compiles a conditional.
    pub(crate) fn gen_cond(&mut self, cond: &ACond) -> CompileResult<()> {
        // Compile each branch, recording whether it returns.
        let mut end_block = None;
        let mut all_branches_return = true;
        let mut all_branches_terminate = true;
        let mut else_branch_exists = false;

        for (i, branch) in cond.branches.iter().enumerate() {
            // If there is a branch condition, it means we are on an `if` or `elsif` branch.
            // Otherwise, it means we're on an `else` branch.
            if let Some(expr) = &branch.cond {
                // Create a "then" block to jump to if the branch condition is true.
                let then_block = self.append_block("cond_branch");

                // Create an `else` block to jump to if the branch condition is false. If this is
                // the last branch in the conditional, the `else` block is the "end" block.
                // Otherwise, we create a new `else` block.
                let else_block = if i + 1 == cond.branches.len() {
                    if end_block.is_none() {
                        end_block = Some(self.append_block("cond_end"));
                    }

                    end_block.unwrap()
                } else {
                    self.append_block("cond_branch")
                };

                // Branch from the current block based on the value of the conditional expression.
                let ll_expr_val = self.gen_expr(expr);
                let ll_cond_val = self.get_bool(ll_expr_val);
                self.builder
                    .build_conditional_branch(ll_cond_val, then_block, else_block);

                // Fill the "then" block with the branch body.
                self.set_current_block(then_block);

                // Create a branch context to store information about the branch being compiled.
                self.push_branch_ctx();

                // Compile the branch body.
                self.gen_closure(&branch.body)?;

                // Pop the branch context now that we're done compiling the branch.
                let ctx = self.pop_ctx().to_branch();

                all_branches_return = all_branches_return && ctx.guarantees_return;
                all_branches_terminate = all_branches_terminate && ctx.guarantees_terminator;

                // If this branch does not end in an unconditional return, we need to complete
                // the corresponding "then" block with an unconditional jump to the "end" block.
                if !ctx.guarantees_terminator {
                    if end_block.is_none() {
                        end_block = Some(self.append_block("cond_end"));
                    }
                    self.builder.build_unconditional_branch(end_block.unwrap());
                }

                // Continue on the `else` block.
                self.set_current_block(else_block);
            } else {
                // This is an else branch, so we must execute the branch body.
                else_branch_exists = true;
                self.push_branch_ctx();
                self.gen_closure(&branch.body)?;
                let ctx = self.pop_ctx().to_branch();
                all_branches_return = all_branches_return && ctx.guarantees_return;
                all_branches_terminate = all_branches_terminate && ctx.guarantees_terminator;

                // If this branch does not end in an unconditional return, we need to complete
                // the current block with an unconditional jump to the "end" block.
                if !ctx.guarantees_terminator {
                    if end_block.is_none() {
                        end_block = Some(self.append_block("cond_end"));
                    }
                    self.builder.build_unconditional_branch(end_block.unwrap());
                }
            }
        }

        // If there is an "end" block, continue on that block.
        if let Some(block) = end_block {
            self.set_current_block(block);
        }

        // Update the parent context with return and terminator information.
        self.set_guarantees_return(all_branches_return && else_branch_exists);
        self.set_guarantees_terminator(all_branches_terminate && else_branch_exists);
        Ok(())
    }
}
