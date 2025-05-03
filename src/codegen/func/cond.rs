use inkwell::basic_block::BasicBlock;
use inkwell::values::{BasicValue, BasicValueEnum, IntValue};

use crate::analyzer::ast::cond::ACond;
use crate::analyzer::ast::r#match::{AMatch, APattern};
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::type_store::{GetType, TypeKey};
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
            self.set_di_location(&branch.span.start_pos);

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
                self.ll_builder
                    .build_conditional_branch(ll_cond_val, then_block, else_block)
                    .unwrap();

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
                    self.ll_builder
                        .build_unconditional_branch(end_block.unwrap())
                        .unwrap();
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
                    self.ll_builder
                        .build_unconditional_branch(end_block.unwrap())
                        .unwrap();
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
            let is_last_case = i + 1 == match_.cases.len();

            // Generate the code for the pattern match expressions, if any.
            let ll_cmp_result = self.gen_pattern_cmp(
                &case.pattern,
                target_tk,
                target_enum_tk,
                ll_target,
                ll_target_variant_num,
                &target_type,
                target_is_signed,
                is_last_case,
            );

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
                    self.ll_builder
                        .build_conditional_branch(ll_result, ll_cond_block, ll_else_block)
                        .unwrap();

                    // Generate code for the condition block.
                    self.set_current_block(ll_cond_block);
                    let ll_cond_value = self.gen_expr(cond);
                    self.ll_builder
                        .build_conditional_branch(
                            ll_cond_value.into_int_value(),
                            ll_then_block,
                            ll_else_block,
                        )
                        .unwrap();

                    Some(ll_else_block)
                }

                // If the pattern matched, branch to the then block. Otherwise, branch to the else
                // block
                (Some(ll_result), None) => {
                    let ll_else_block = self.append_block(format!("match_case_{}", i + 1).as_str());
                    self.ll_builder
                        .build_conditional_branch(ll_result, ll_then_block, ll_else_block)
                        .unwrap();
                    Some(ll_else_block)
                }

                // There is no pattern, so just evaluate the condition and branch based on that.
                (None, Some(cond)) => {
                    let ll_else_block = self.append_block(format!("match_case_{}", i + 1).as_str());

                    // Generate code for the condition.
                    let ll_cond_value = self.gen_expr(cond);
                    self.ll_builder
                        .build_conditional_branch(
                            ll_cond_value.into_int_value(),
                            ll_then_block,
                            ll_else_block,
                        )
                        .unwrap();

                    Some(ll_else_block)
                }

                // Just branch directly to the then block.
                (None, None) => {
                    self.ll_builder
                        .build_unconditional_branch(ll_then_block)
                        .unwrap();
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
                self.ll_builder
                    .build_unconditional_branch(ll_match_end_block.unwrap())
                    .unwrap();
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

    /// Generates code that compares a pattern to a match target. Returns the result of the
    /// comparison, if any.
    fn gen_pattern_cmp(
        &mut self,
        pattern: &APattern,
        target_tk: TypeKey,
        target_enum_tk: TypeKey,
        ll_target: BasicValueEnum<'ctx>,
        ll_target_variant_num: Option<IntValue<'ctx>>,
        target_type: &AType,
        target_is_signed: bool,
        is_last_case: bool,
    ) -> Option<IntValue<'ctx>> {
        match pattern {
            APattern::Exprs(exprs) => {
                let mut exprs_iter = exprs.iter();
                let mut ll_phi_args = vec![];

                // Generate the first comparison expression.
                let ll_expr = self.gen_expr(exprs_iter.next()?);
                let mut ll_cmp_result = self.gen_cmp_op(
                    ll_expr,
                    target_tk,
                    &Operator::EqualTo,
                    ll_target,
                    target_is_signed,
                );
                ll_phi_args.push((ll_cmp_result.as_basic_value_enum(), self.cur_block?));
                let ll_end_block = self.append_block("pattern_end");

                // Generate remaining comparison expressions.
                while let Some(expr) = exprs_iter.next() {
                    let ll_next_pattern_block = self.append_block("next_pattern");
                    self.ll_builder
                        .build_conditional_branch(
                            ll_cmp_result,
                            ll_end_block,
                            ll_next_pattern_block,
                        )
                        .unwrap();

                    self.set_current_block(ll_next_pattern_block);
                    let ll_expr = self.gen_expr(expr);
                    ll_cmp_result = self.gen_cmp_op(
                        ll_expr,
                        target_tk,
                        &Operator::EqualTo,
                        ll_target,
                        target_is_signed,
                    );
                    ll_phi_args.push((ll_cmp_result.as_basic_value_enum(), self.cur_block?));
                }

                // Branch to the pattern end block and build a phi node that gets results from
                // the expression comparison blocks.
                self.ll_builder
                    .build_unconditional_branch(ll_end_block)
                    .unwrap();
                self.set_current_block(ll_end_block);
                let ll_phi_val = self
                    .ll_builder
                    .build_phi(self.ll_ctx.bool_type(), "pattern_phi")
                    .unwrap();
                for (ll_phi_arg, ll_block) in ll_phi_args {
                    ll_phi_val.add_incoming(&[(&ll_phi_arg, ll_block)]);
                }

                match is_last_case {
                    true => None,
                    false => Some(ll_phi_val.as_basic_value().into_int_value()),
                }
            }

            APattern::LetSymbol(_, var_name) => {
                self.create_var(var_name, target_tk, ll_target);
                None
            }

            APattern::LetEnumVariants(_, var_name, var_tk, variant_nums) => {
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
                match is_last_case {
                    // Last case.
                    true => None,

                    // Not last case.
                    false => {
                        let ll_target_variant = ll_target_variant_num?;
                        let ll_num_type = ll_target_variant.get_type();

                        let ll_match_block = self.append_block("variant_matched");
                        let ll_no_match_block = self.append_block("no_variant_matched");
                        let ll_end_block = self.append_block("variant_check_end");

                        let ll_switch_cases: Vec<(IntValue, BasicBlock)> = variant_nums
                            .iter()
                            .map(|num| (ll_num_type.const_int(*num as u64, false), ll_match_block))
                            .collect();
                        self.ll_builder
                            .build_switch(ll_target_variant, ll_no_match_block, &ll_switch_cases)
                            .unwrap();

                        self.set_current_block(ll_match_block);
                        self.ll_builder
                            .build_unconditional_branch(ll_end_block)
                            .unwrap();

                        self.set_current_block(ll_no_match_block);
                        self.ll_builder
                            .build_unconditional_branch(ll_end_block)
                            .unwrap();

                        self.set_current_block(ll_end_block);
                        let ll_bool_type = self.ll_ctx.bool_type();
                        let ll_phi = self
                            .ll_builder
                            .build_phi(ll_bool_type, "found_variant_match")
                            .unwrap();

                        let ll_true = ll_bool_type.const_int(1, false);
                        let ll_false = ll_bool_type.const_int(0, false);
                        ll_phi.add_incoming(&[(&ll_true.as_basic_value_enum(), ll_match_block)]);
                        ll_phi
                            .add_incoming(&[(&ll_false.as_basic_value_enum(), ll_no_match_block)]);

                        Some(ll_phi.as_basic_value().into_int_value())
                    }
                }
            }

            APattern::Wildcard => None,
        }
    }
}
