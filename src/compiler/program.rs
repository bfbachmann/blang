use std::collections::HashMap;
use std::path::Path;

use inkwell::attributes::{Attribute, AttributeLoc};
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::passes::PassManager;
use inkwell::targets::TargetTriple;
use inkwell::types::AnyType;
use inkwell::values::FunctionValue;

use crate::analyzer::func::RichFnSig;
use crate::analyzer::program::{ProgramAnalysis, RichProg};
use crate::analyzer::r#type::{RichType, TypeId};
use crate::analyzer::statement::RichStatement;
use crate::compiler::convert;
use crate::compiler::error::{CompileError, CompileResult, ErrorKind};
use crate::compiler::func::FnCompiler;

/// Compiles a type-rich and semantically valid program to LLVM IR and/or bitcode.
pub struct ProgCompiler<'a, 'ctx> {
    ctx: &'ctx Context,
    builder: &'a Builder<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    module: &'a Module<'ctx>,
    program: &'a RichProg,
    types: &'a HashMap<TypeId, RichType>,
}

impl<'a, 'ctx> ProgCompiler<'a, 'ctx> {
    /// Compiles the program for the given target. If there is no target, compiles the program for
    /// the host system.
    pub fn compile(
        prog_analysis: ProgramAnalysis,
        target_triple: Option<&String>,
        as_bitcode: bool,
        output_path: &Path,
        simplify_ir: bool,
    ) -> CompileResult<()> {
        // Error if the program analysis contains errors (meaning it didn't pass semantic analysis.
        if !prog_analysis.errors.is_empty() {
            return Err(CompileError::new(
                ErrorKind::InvalidProgram,
                "cannot compile program that failed semantic analysis",
            ));
        }

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
            ctx: &ctx,
            builder: &builder,
            fpm: &fpm,
            module: &module,
            program: &prog_analysis.prog,
            types: &prog_analysis.types,
        };
        compiler.compile_program()?;

        // Write output as to file.
        if as_bitcode {
            compiler.module.write_bitcode_to_path(output_path);
        } else {
            if let Err(e) = compiler.module.print_to_file(output_path) {
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
                    FnCompiler::compile(
                        self.ctx,
                        self.builder,
                        self.fpm,
                        self.module,
                        self.types,
                        func,
                    )?;
                }
                RichStatement::StructTypeDeclaration(_) => {
                    // Nothing to do here because struct types are compiled only when they're used.
                }
                RichStatement::ExternFnDeclaration(_) => {
                    // Nothing to do here because extern functions are compiled in the call to
                    // `ProgramCompiler::define_extern_fns` above.
                }
                other => {
                    panic!("unexpected top-level statement {other}");
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
        let fn_type = convert::to_fn_type(self.ctx, self.types, sig);
        let fn_val = self.module.add_function(sig.name.as_str(), fn_type, None);

        // Set arg names and mark arguments as pass-by-value where necessary.
        if fn_val.count_params() == sig.args.len() as u32 {
            // The compiled function arguments match those of the original function signature, so
            // just assign arg names normally.
            for (arg_val, arg) in fn_val.get_param_iter().zip(sig.args.iter()) {
                arg_val.set_name(arg.name.as_str());
            }
        } else {
            // The compiled function arguments do not match those of the original function
            // signature. This means the function is taking an additional pointer as its first
            // argument, to which the result will be written. This is done for functions that
            // return structured types.
            let first_arg_val = fn_val.get_first_param().unwrap();
            first_arg_val.set_name("ret_val_ptr");

            // Add the "sret" attribute to the first argument to tell LLVM that it is being used to
            // pass the return value.
            self.add_fn_arg_attrs(fn_val, 0, vec!["sret"]);

            // Name the remaining function arguments normally.
            for i in 1..fn_val.count_params() {
                let arg_val = fn_val.get_nth_param(i).unwrap();
                arg_val.set_name(sig.args.get((i - 1) as usize).unwrap().name.as_str());
            }
        }
    }

    /// Adds the given attributes to the function argument at the given index.
    fn add_fn_arg_attrs(&self, fn_val: FunctionValue<'ctx>, arg_index: u32, attrs: Vec<&str>) {
        let param = fn_val.get_nth_param(arg_index).unwrap();
        let param_type = param.get_type().as_any_type_enum();

        for attr in attrs {
            let attr_kind = Attribute::get_named_enum_kind_id(attr);
            // Make sure the attribute is properly defined.
            assert_ne!(attr_kind, 0);
            let attr = self.ctx.create_type_attribute(attr_kind, param_type);
            fn_val.add_attribute(AttributeLoc::Param(arg_index), attr);
        }
    }

    /// Defines external functions in the current module.
    fn define_extern_fns(&mut self) {
        for statement in &self.program.statements {
            if let RichStatement::ExternFnDeclaration(fn_sig) = statement {
                let fn_type = convert::to_fn_type(self.ctx, self.types, &fn_sig);
                self.module
                    .add_function(fn_sig.name.as_str(), fn_type, Some(Linkage::External));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Cursor};
    use std::path::Path;

    use crate::analyzer::program::RichProg;
    use crate::compiler::program::ProgCompiler;
    use crate::lexer::token::Token;
    use crate::parser::program::Program;
    use crate::parser::stream::Stream;

    fn assert_compiles(code: &str) {
        let tokens = Token::tokenize(Cursor::new(code).lines()).expect("should not error");
        let prog = Program::from(&mut Stream::from(tokens)).expect("should not error");
        let analysis = RichProg::analyze(prog);
        ProgCompiler::compile(analysis, None, false, Path::new("/dev/null"), false)
            .expect("should not error");
    }

    #[test]
    fn basic_program() {
        assert_compiles(
            r#"
            fn main() {
                let val = other(2, 10)
                fib(val)
                
                let hi = "hello world!!"
                str_stuff("test")
            }
            
            fn thing(b: bool): bool {
                let a = true
                return !a || b
            }
            
            fn other(a: i64, b: i64): i64 {
                return a * b + a / 2 - 1
            }
            
            fn fib(n: i64): i64 {
                if n < 2 {
                    return 1
                }
                
                return fib(n-1) + fib(n-2)
            }
            
            fn do_thing(a: i64): i64 {
                let mut result = 5
                let mut mut_a = a
                loop {
                    if mut_a < 10 {
                        loop {
                            result = result + 1
                            if result > 100 {
                                mut_a = mut_a / 2
                                break
                            } else {
                                continue
                            }
                        }
                    }
                    
                    return mut_a * result
                }
            }
            
            fn cum_sum(n: i64): i64 {
                let mut i = 1
                let mut result = 0
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
            
            fn str_stuff(s: str): str {
                return "test"
            }
        "#,
        );
    }

    #[test]
    fn struct_init() {
        assert_compiles(
            r#"
            struct Person {
                name: str,
                age: i64,
                do_thing: fn(str): i64,
            }
            
            fn new_person(name: str, age: i64): Person {
                return Person{
                    name: name,
                    age: age,
                    do_thing: test
                }
            }
            
            fn test(s: str): i64 {
                return 1
            }
            
            fn main() {
                let p = Person{
                    name: "test",
                    age: 12,
                    do_thing: test,
                }
            
                let pp = new_person("guy", 32)
            }
        "#,
        );
    }

    #[test]
    fn struct_pass_by_value() {
        assert_compiles(
            r#"
            struct Person {
                age: i64,
            }
            
            fn is_old(p: Person): bool {
                let p = Person{age: 100}
                return false
            }
            
            fn main() {
                let mut p = Person{age: 10}
                is_old(p)
                p = Person{age: 1}
            }
        "#,
        );
    }

    #[test]
    fn uses_externs() {
        assert_compiles(
            r#"
            ext fn write(fd: i64, msg: str, len: i64)
            ext fn exit(code: i64)
            
            fn main() {
                write(1, "Hello World!", 13) 
                exit(0)
            }
       "#,
        );
    }

    #[test]
    fn valid_type_def_cycle() {
        assert_compiles(
            r#"
            struct A {
                count: i64,
                f: fn(A),
            }
            
            fn do(a: A) {}
            
            fn new_a(count: i64): A {
                return A {
                    count: count,
                    f: do,
                }
            }"#,
        )
    }

    #[test]
    fn infinite_loop() {
        assert_compiles(
            r#"
        fn main() {
            loop {}
        }
        "#,
        );
    }
}
