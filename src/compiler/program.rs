use std::path::Path;

use crate::analyzer::func::RichFnSig;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::passes::PassManager;
use inkwell::targets::TargetTriple;
use inkwell::types::{AsTypeRef, BasicMetadataTypeEnum, FunctionType};
use inkwell::values::FunctionValue;
use llvm_sys::core::LLVMFunctionType;
use llvm_sys::prelude::LLVMTypeRef;

use crate::analyzer::program::RichProg;
use crate::analyzer::statement::RichStatement;
use crate::compiler::convert;
use crate::compiler::error::{CompileError, CompileResult, ErrorKind};
use crate::compiler::func::FnCompiler;

/// Compiles a type-rich and semantically valid program to LLVM IR and/or bitcode.
pub struct ProgCompiler<'a, 'ctx> {
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    module: &'a Module<'ctx>,
    program: &'a RichProg,
}

impl<'a, 'ctx> ProgCompiler<'a, 'ctx> {
    /// Compiles the program for the given target. If there is no target, compiles the program for
    /// the host system.
    pub fn compile(
        program: &RichProg,
        target_triple: Option<&String>,
        bitcode_output_path: Option<&String>,
        ir_output_path: Option<&String>,
        simplify_ir: bool,
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
        if simplify_ir {
            fpm.add_instruction_combining_pass();
            fpm.add_reassociate_pass();
            fpm.add_gvn_pass();
            fpm.add_cfg_simplification_pass();
            fpm.add_basic_alias_analysis_pass();
            fpm.add_promote_memory_to_register_pass();
            fpm.add_instruction_combining_pass();
            fpm.add_reassociate_pass();
        }
        fpm.initialize();

        // Create the program compiler and compile the program.
        let mut compiler = ProgCompiler {
            context: &ctx,
            builder: &builder,
            fpm: &fpm,
            module: &module,
            program,
        };

        compiler.compile_program()?;

        // Optionally write output as bitcode to file.
        if let Some(path) = bitcode_output_path {
            compiler.module.write_bitcode_to_path(Path::new(path));
        }

        // Optionally write output as IR to file.
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
        // Define external functions (like syscalls) so we can call the safely from within the
        // module. Their actual implementations should be linked from libc when generating an
        // executable.
        self.define_extern_fns();

        // Do one shallow pass to define all top-level functions in the module.
        for statement in &self.program.statements {
            match statement {
                RichStatement::FunctionDeclaration(func) => {
                    self.compile_fn_sig(&func.signature);
                }
                _ => {}
            }
        }

        // Compile all the statements in the program.
        for statement in &self.program.statements {
            match statement {
                RichStatement::FunctionDeclaration(func) => {
                    FnCompiler::compile(self.context, self.builder, self.fpm, self.module, func)?;
                }
                RichStatement::StructTypeDeclaration(_s) => {
                    // TODO
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
    fn compile_fn_sig(&self, sig: &RichFnSig) {
        // Define the function in the module.
        let fn_type = self.create_fn_type(sig);
        let fn_val = self.module.add_function(sig.name.as_str(), fn_type, None);

        // Set arg names.
        for (arg_val, arg) in fn_val.get_param_iter().zip(sig.args.iter()) {
            arg_val.set_name(arg.name.as_str());
        }
    }

    /// Converts a `FunctionSignature` into an LLVM `FunctionType`.
    fn create_fn_type(&self, sig: &RichFnSig) -> FunctionType<'ctx> {
        // Get return type.
        let ret_type = convert::to_any_type(self.context, sig.return_type.as_ref());

        // Get arg types.
        let arg_types = sig
            .args
            .iter()
            .map(|a| convert::to_metadata_type_enum(self.context, &a.typ))
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

    /// Defines external functions in the current module.
    fn define_extern_fns(&mut self) {
        for extern_fn_sig in &self.program.extern_fns {
            let fn_type = self.create_fn_type(&extern_fn_sig);
            self.module.add_function(
                extern_fn_sig.name.as_str(),
                fn_type,
                Some(Linkage::External),
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Cursor};

    use crate::analyzer::program::RichProg;
    use crate::compiler::program::ProgCompiler;
    use crate::lexer::token::Token;
    use crate::parser::program::Program;
    use crate::syscall::syscall::all_syscalls;

    #[test]
    fn basic_program() {
        let code = r#"
            fn main() {
                i64 val = other(2, 10)
                fib(val)
                
                string hi = "hello world!!"
                string_stuff("test")
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
            
            fn do_thing(i64 a): i64 {
                i64 result = 5
                loop {
                    if a < 10 {
                        loop {
                            result = result + 1
                            if result > 100 {
                                a = a / 2
                                break
                            } else {
                                continue
                            }
                        }
                    }
                    
                    return a * result
                }
            }
            
            fn cum_sum(i64 n): i64 {
                i64 i = 1
                i64 result = 0
                loop {
                    if i >= n {
                        return result 
                    }
                
                    {{
                        result = result + i
                        i = i + 1
                    }}
                }
            }
            
            fn string_stuff(string s): string {
                return "test"
            }
        "#;
        let mut tokens = Token::tokenize(Cursor::new(code).lines()).expect("should not error");
        let prog = Program::from(&mut tokens).expect("should not error");
        let rich_prog = RichProg::from(prog, all_syscalls().to_vec()).expect("should not error");
        ProgCompiler::compile(&rich_prog, None, None, None, false).expect("should not error");
    }
}
