use inkwell::values::BasicValue;

use crate::analyzer::ast::cond::ACond;
use crate::analyzer::ast::r#match::{AMatch, APattern};
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::type_store::GetType;
use crate::codegen::error::CodeGenResult;
use crate::parser::ast::op::Operator;

use super::FnCodeGen;

impl<'a, 'ctx> FnCodeGen<'a, 'ctx> {
    /// Compiles a conditional.
    pub(crate) fn gen_cond(&mut self, cond: &ACond) -> CodeGenResult<()> {
        // Compile each branch, recording whether it returns.
        let mut end_block = None;
        let mut all_branches_return = true;
        let mut all_branches_terminate = true;
        let mut else_branch_exists = false;

        for (i, branch) in cond.branches.iter().enumerate() {
            // If there is a branch condition, it means we are on an `if` or `else if` branch.
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

                let has_terminator = self.current_block_has_terminator();
                all_branches_return = all_branches_return && ctx.guarantees_return;
                all_branches_terminate = all_branches_terminate && has_terminator;

                // If this branch does not end in an unconditional return, we need to complete
                // the corresponding "then" block with an unconditional jump to the "end" block.
                if !has_terminator {
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
                let has_terminator = self.current_block_has_terminator();
                all_branches_return = all_branches_return && ctx.guarantees_return;
                all_branches_terminate = all_branches_terminate && has_terminator;

                // If this branch does not end in an unconditional return, we need to complete
                // the current block with an unconditional jump to the "end" block.
                if !has_terminator {
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

    /// Generates code for a match statement.
    pub(crate) fn gen_match(&mut self, match_: &AMatch) -> CodeGenResult<()> {
        // Generate the target expression.
        let ll_target = self.gen_expr(&match_.target);
        let target_tk = match_.target.type_key;
        let target_type = self.type_converter.get_type(target_tk).clone();
        let target_is_signed = target_type.is_signed();

        // If the target expression is an enum value, we'll also preemptively extract its variant
        // number, so we can check against it.
        let (ll_target_variant_num, target_enum_tk) = match &target_type {
            AType::Enum(_) => (
                Some(self.get_enum_variant_number(target_tk, ll_target)),
                target_tk,
            ),

            AType::Pointer(ptr_type) => {
                let pointee_tk = ptr_type.pointee_type_key;
                match self.type_converter.get_type(pointee_tk) {
                    AType::Enum(_) => (
                        Some(self.get_enum_variant_number(pointee_tk, ll_target)),
                        pointee_tk,
                    ),
                    _ => (None, target_tk),
                }
            }

            _ => (None, target_tk),
        };

        let mut ll_match_end_block = None;

        // Generate code for each match case.
        for (i, case) in match_.cases.iter().enumerate() {
            // Generate the code for the pattern match expression, if any.
            let ll_cmp_result = match &case.pattern {
                APattern::Expr(expr) => {
                    let ll_expr = self.gen_expr(expr);
                    let ll_result = self.gen_cmp_op(
                        ll_expr,
                        target_tk,
                        &Operator::EqualTo,
                        ll_target,
                        target_is_signed,
                    );
                    Some(ll_result)
                }

                APattern::LetEnumVariant(_, var_name, var_tk, variant_num) => {
                    // Assign the enum inner value to the bound variable in the pattern if it's not
                    // a wildcard.
                    if !var_name.is_empty() {
                        // Extract the value from inside the enum.
                        let (load_ptr, var_tk) = match target_type {
                            AType::Pointer(_) => (true, target_tk),
                            _ => (false, *var_tk),
                        };
                        let ll_inner_val =
                            self.get_enum_inner_val(target_enum_tk, var_tk, ll_target, load_ptr);
                        self.create_var(var_name, var_tk, ll_inner_val);
                    }

                    // Don't do a comparison if this is the last case, as it's guaranteed
                    // to match anyway (because match cases are exhaustive).
                    match i + 1 == match_.cases.len() {
                        // Last case.
                        true => None,

                        // Not last case.
                        false => {
                            let ll_target_variant = ll_target_variant_num.unwrap();
                            let ll_num_type = ll_target_variant.get_type();
                            let ll_pattern_variant =
                                ll_num_type.const_int(*variant_num as u64, false);
                            let ll_result = self.gen_int_cmp(
                                &Operator::EqualTo,
                                ll_target_variant.as_basic_value_enum(),
                                ll_pattern_variant.as_basic_value_enum(),
                                false,
                            );

                            Some(ll_result)
                        }
                    }
                }

                APattern::Wildcard => None,
            };

            // Generate code to branch based on whether the pattern matched.
            let ll_then_block = self.append_block(format!("match_case_{i}_then").as_str());
            let ll_else_block = match (ll_cmp_result, &case.maybe_cond) {
                // If the pattern matched, branch to the condition block. From the condition block,
                // we'll branch to the then block or the else block based on the condition.
                (Some(ll_result), Some(cond)) => {
                    // Branch to the conditional block if the pattern matches, otherwise branch to
                    // the else block.
                    let ll_cond_block = self.append_block(format!("match_cond_{i}_if").as_str());
                    let ll_else_block = self.append_block(format!("match_case_{}", i + 1).as_str());
                    self.builder
                        .build_conditional_branch(ll_result, ll_cond_block, ll_else_block);

                    // Generate code for the condition block.
                    self.set_current_block(ll_cond_block);
                    let ll_cond_value = self.gen_expr(cond);
                    self.builder.build_conditional_branch(
                        ll_cond_value.into_int_value(),
                        ll_then_block,
                        ll_else_block,
                    );

                    Some(ll_else_block)
                }

                // If the pattern matched, branch to the then block. Otherwise, branch to the else
                // block
                (Some(ll_result), None) => {
                    let ll_else_block = self.append_block(format!("match_case_{}", i + 1).as_str());
                    self.builder
                        .build_conditional_branch(ll_result, ll_then_block, ll_else_block);
                    Some(ll_else_block)
                }

                // There is no pattern, so just evaluate the condition and branch based on that.
                (None, Some(cond)) => {
                    let ll_else_block = self.append_block(format!("match_case_{}", i + 1).as_str());

                    // Generate code for the condition.
                    let ll_cond_value = self.gen_expr(cond);
                    self.builder.build_conditional_branch(
                        ll_cond_value.into_int_value(),
                        ll_then_block,
                        ll_else_block,
                    );

                    Some(ll_else_block)
                }

                // Just branch directly to the then block.
                (None, None) => {
                    self.builder.build_unconditional_branch(ll_then_block);
                    None
                }
            };

            // Generate code for the match case body.
            self.set_current_block(ll_then_block);
            self.gen_closure(&case.body)?;

            // Branch to match end block if there is no terminator.
            if !self.current_block_has_terminator() {
                ll_match_end_block = match ll_match_end_block {
                    None => Some(self.append_block("match_end")),
                    some => some,
                };
                self.builder
                    .build_unconditional_branch(ll_match_end_block.unwrap());
            }

            // If there is an else block, switch to it so we can use it to generate code for the
            // next case.
            match ll_else_block {
                Some(ll_else_block) => {
                    self.set_current_block(ll_else_block);
                }
                None => break,
            };
        }

        // Switch to the end block, if there is one.
        if let Some(ll_end_block) = ll_match_end_block {
            self.set_current_block(ll_end_block);
        }

        Ok(())
    }
}
