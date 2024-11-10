use inkwell::values::BasicValue;

use crate::analyzer::ast::r#yield::AYield;
use crate::analyzer::ast::ret::ARet;
use crate::analyzer::ast::statement::AStatement;
use crate::analyzer::type_store::GetType;
use crate::codegen::error::CodeGenResult;

use super::FnCodeGen;

impl<'a, 'ctx> FnCodeGen<'a, 'ctx> {
    /// Compiles a statement.
    pub(crate) fn gen_statement(&mut self, statement: &AStatement) -> CodeGenResult<()> {
        match statement {
            AStatement::VariableDeclaration(var_decl) => {
                // Get the value of the expression being assigned to the variable.
                let ll_expr_val = self.gen_expr(&var_decl.val);

                // Create and initialize the variable.
                self.create_var(var_decl.name.as_str(), var_decl.type_key, ll_expr_val);
            }
            AStatement::StructTypeDeclaration(_) | AStatement::EnumTypeDeclaration(_) => {
                // Nothing to do here. Types are compiled upon initialization.
            }
            AStatement::VariableAssignment(assign) => {
                self.assign_var(assign);
            }
            AStatement::FunctionDeclaration(_) => {
                // No need to generate any code here. The mono item collector would have already
                // walked this function and created mono items for it, so we'll generate it in
                // `gen_program` anyway.
            }
            AStatement::Closure(closure) => {
                self.gen_closure(closure)?;
            }
            AStatement::FunctionCall(call) => {
                self.gen_call(call);
            }
            AStatement::Conditional(cond) => {
                self.gen_cond(cond)?;
            }
            AStatement::Loop(closure) => {
                self.gen_loop(closure)?;
            }
            AStatement::Break => {
                self.gen_break();
            }
            AStatement::Continue => {
                self.gen_continue();
            }
            AStatement::Return(ret) => {
                self.gen_return(ret);
            }
            AStatement::Yield(yld) => {
                self.gen_yield(yld);
            }
            AStatement::Const(const_decl) => {
                self.local_consts
                    .insert(const_decl.name.clone(), const_decl.clone());
            }
            AStatement::ExternFn(_) => {
                // Nothing to do here. This is already handled in
                // `ProgramCodeGen::gen_program`.
            }
            AStatement::Impl(_) => {
                // These blocks should not occur inside functions.
                unreachable!();
            }
        };

        Ok(())
    }

    /// Compiles a return statement.
    fn gen_return(&mut self, ret: &ARet) {
        self.set_guarantees_return(true);
        self.set_loop_contains_return(true);

        match &ret.val {
            // Compile the return expression.
            Some(expr) => {
                let result = self.gen_expr(expr);

                // If the value being returned is some structured type, we need to copy it to the
                // memory pointed to by the first argument and return void.
                let ret_type_key = self.type_converter.map_type_key(expr.type_key);
                let expr_type = self.type_store.get_type(ret_type_key);
                if expr_type.is_composite() {
                    // Copy the return value into the pointer from the first function argument.
                    let ll_ret_ptr = self.fn_value.unwrap().get_first_param().unwrap();
                    self.copy_value(result, ll_ret_ptr.into_pointer_value(), ret_type_key);

                    // Return void.
                    self.builder.build_return(None);
                } else {
                    self.builder.build_return(Some(&result));
                }
            }

            // The function has no return type, so return void.
            None => {
                self.builder.build_return(None);
            }
        }
    }

    /// Compiles a yield statement.
    fn gen_yield(&mut self, yld: &AYield) {
        // Compile the yielded value expression.
        let mut result = self.gen_expr(&yld.value);

        // If the result is a composite value, we need to make sure we're
        // yielding it as a pointer. It may currently be a constant, in
        // which case we must stack-allocate it, so we can yield a pointer to it.
        // Otherwise, we could run into cases were values of the same type are
        // being yielded from the same `from` expression both as pointers and
        // immediate aggregate values, which would cause LLVM to error because
        // of the type inconsistency in the phi node that receives yielded results.
        let is_composite_type = self
            .type_converter
            .get_type(yld.value.type_key)
            .is_composite();
        let is_const = !result.is_pointer_value();
        if is_composite_type && is_const {
            let ll_ptr = self.stack_alloc("yielded_value", yld.value.type_key);
            self.copy_value(result, ll_ptr, yld.value.type_key);
            result = ll_ptr.as_basic_value_enum();
        }

        // Append the yielded value to the `from` context so we can use it in the
        // phi node at the `from` end block and build a branch to the end block.
        let ll_block = self.cur_block.unwrap();
        let ctx = self.get_from_ctx();
        ctx.yielded_vales.insert(ll_block, result);

        let ll_end_block = ctx.end_block;
        self.builder.build_unconditional_branch(ll_end_block);
    }
}
