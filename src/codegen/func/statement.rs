use crate::analyzer::ast::ret::ARet;
use crate::analyzer::ast::statement::AStatement;
use crate::codegen::error::CompileResult;

use super::{gen_fn_sig, FnCodeGen};

impl<'a, 'ctx> FnCodeGen<'a, 'ctx> {
    /// Compiles a statement.
    pub(crate) fn gen_statement(&mut self, statement: &AStatement) -> CompileResult<()> {
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
            AStatement::FunctionDeclaration(func) => {
                // Declare and compile the new function.
                gen_fn_sig(self.ctx, self.module, self.type_converter, &func.signature);
                self.gen_nested_fn(func);
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
            AStatement::Consts(consts) => {
                for c in consts {
                    self.local_consts.insert(c.name.clone(), c.clone());
                }
            }
            AStatement::ExternFns(_) => {
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
                let expr_type = self.type_store.must_get(expr.type_key);
                if expr_type.is_composite() {
                    // Copy the return value into the pointer from the first function argument.
                    let ll_ret_ptr = self.fn_value.unwrap().get_first_param().unwrap();
                    self.copy_value(result, ll_ret_ptr.into_pointer_value(), expr.type_key);

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
}
