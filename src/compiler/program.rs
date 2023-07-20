use crate::analyzer::program::RichProg;
use crate::analyzer::statement::RichStatement;
use crate::compiler::error::{CompileError, CompileResult, ErrorKind};
use crate::compiler::func;
use crate::compiler::func::FnCompiler;
use crate::parser::func_sig::FunctionSignature;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::targets::TargetTriple;
use inkwell::types::{AsTypeRef, BasicMetadataTypeEnum, FunctionType};
use inkwell::values::FunctionValue;
use llvm_sys::core::LLVMFunctionType;
use llvm_sys::prelude::LLVMTypeRef;
use std::path::Path;

pub struct Compiler<'a, 'ctx> {
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    module: &'a Module<'ctx>,
    program: &'a RichProg,
}

impl<'a, 'ctx> Compiler<'a, 'ctx> {
    /// Compiles the program for the given target. If there is no target, compiles the program for
    /// the host system.
    pub fn compile(
        program: &RichProg,
        target_triple: Option<&String>,
        bitcode_output_path: Option<&String>,
        ir_output_path: Option<&String>,
    ) -> CompileResult<()> {
        let ctx = Context::create();
        let builder = ctx.create_builder();
        let module = ctx.create_module("main");

        // Set target triple, if one was provided.
        if let Some(target) = target_triple {
            module.set_triple(&TargetTriple::create(target));
        }

        // Set up function pass manager.
        let fpm = PassManager::create(&module);
        fpm.add_instruction_combining_pass();
        fpm.add_reassociate_pass();
        fpm.add_gvn_pass();
        fpm.add_cfg_simplification_pass();
        fpm.add_basic_alias_analysis_pass();
        fpm.add_promote_memory_to_register_pass();
        fpm.add_instruction_combining_pass();
        fpm.add_reassociate_pass();
        fpm.initialize();

        let mut compiler = Compiler {
            context: &ctx,
            builder: &builder,
            fpm: &fpm,
            module: &module,
            program,
        };

        compiler.compile_program()?;

        if let Some(path) = bitcode_output_path {
            compiler.module.write_bitcode_to_path(Path::new(path));
        }

        if let Some(path) = ir_output_path {
            if let Err(e) = compiler.module.print_to_file(Path::new(path)) {
                return Err(CompileError::new(
                    ErrorKind::WriteOutFailed,
                    e.to_string().as_str(),
                ));
            }
        }

        Ok(())
    }

    /// Compiles the program.
    fn compile_program(&mut self) -> CompileResult<()> {
        // Do one shallow pass to define all top-level functions in the module.
        for statement in &self.program.statements {
            match statement {
                RichStatement::FunctionDeclaration(func) => {
                    self.compile_fn_sig(&func.signature);
                }
                _ => {}
            }
        }

        for statement in &self.program.statements {
            match statement {
                RichStatement::FunctionDeclaration(func) => {
                    FnCompiler::compile(self.context, self.builder, self.fpm, self.module, func)?;
                }
                other => {
                    panic!("top-level statement {other} not implemented");
                }
            }
        }

        if let Err(e) = self.module.verify() {
            panic!("module verification failed: {}", e);
        }

        Ok(())
    }

    /// Defines the given function in the current module based on the function signature.
    fn compile_fn_sig(&self, sig: &FunctionSignature) {
        // Define the function in the module.
        let fn_type = self.create_fn_type(sig);
        let fn_val = self.module.add_function(sig.name.as_str(), fn_type, None);

        // Set arg names.
        for (arg_val, arg) in fn_val.get_param_iter().zip(sig.args.iter()) {
            arg_val.set_name(arg.name.as_str());
        }
    }

    /// Converts a `FunctionSignature` into an LLVM `FunctionType`.
    fn create_fn_type(&self, sig: &FunctionSignature) -> FunctionType<'ctx> {
        // Get return type.
        let ret_type = func::get_any_type(self.context, sig.return_type.as_ref());

        // Get arg types.
        let arg_types = sig
            .args
            .iter()
            .map(|a| func::metadata_type_enum(self.context, &a.typ))
            .collect::<Vec<BasicMetadataTypeEnum>>();

        // Create the function type.
        let mut param_types: Vec<LLVMTypeRef> =
            arg_types.iter().map(|val| val.as_type_ref()).collect();
        unsafe {
            FunctionType::new(LLVMFunctionType(
                ret_type.as_type_ref(),
                param_types.as_mut_ptr(),
                param_types.len() as u32,
                false as i32,
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Cursor};

    use crate::analyzer::program::RichProg;
    use crate::compiler::program::Compiler;
    use crate::lexer::token::Token;
    use crate::parser::program::Program;

    #[test]
    fn basic_program() {
        let code = r#"
            fn main() {
                i64 val = other(2, 10)
                fib(val)
            }
            
            fn thing(bool b): bool {
                bool a = true
                return !a || b
            }
            
            fn other(i64 a, i64 b): i64 {
                return a * b + a / 2 - 1
            }
            
            fn fib(i64 n): i64 {
                if n < 2 {
                    return 1
                }
                
                return fib(n-1) + fib(n-2)
            }
            
            fn cum_sum(i64 n): i64 {
                i64 i = 1
                i64 result = 0
                loop {
                    if i >= n {
                        return result 
                    }
                
                    result = result + i
                    i = i + 1
                }
            }
        "#;
        let mut tokens = Token::tokenize(Cursor::new(code).lines()).expect("should not error");
        let prog = Program::from(&mut tokens).expect("should not error");
        let rich_prog = RichProg::from(prog).expect("should not error");
        Compiler::compile(&rich_prog, None, None, None).expect("should not error");
    }
}
