use std::collections::HashMap;
use std::path::Path;

use inkwell::attributes::{Attribute, AttributeLoc};
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::passes::PassManager;
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple,
};
use inkwell::types::AnyType;
use inkwell::values::FunctionValue;
use inkwell::OptimizationLevel;

use crate::analyzer::ast::func::AFnSig;
use crate::analyzer::ast::r#const::AConst;
use crate::analyzer::ast::source::ASource;
use crate::analyzer::ast::statement::AStatement;
use crate::analyzer::type_store::TypeStore;
use crate::codegen::convert::TypeConverter;
use crate::codegen::error::{CodeGenError, CompileResult, ErrorKind};
use crate::codegen::func::FnCodeGen;

/// Compiles a type-rich and semantically valid program to LLVM IR and/or bitcode.
pub struct ProgramCodeGen<'a, 'ctx> {
    ctx: &'ctx Context,
    builder: &'a Builder<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    module: &'a Module<'ctx>,
    program: &'a ASource,
    type_store: &'a TypeStore,
    type_converter: TypeConverter<'ctx>,
    module_consts: HashMap<String, AConst>,
}

/// The type of output file to generate.
pub enum OutputFormat {
    LLVMBitcode,
    LLVMIR,
    Assembly,
    Object,
}

impl<'a, 'ctx> ProgramCodeGen<'a, 'ctx> {
    /// Compiles the program to LLVM IR.
    fn gen_program(&mut self) -> CompileResult<()> {
        // Define external functions (like syscalls) so we can call the safely from within the
        // module. Their actual implementations should be linked from libc when generating an
        // executable.
        self.define_extern_fns();

        // Defined constants so they can be used inside the functions we compile later.
        self.define_consts();

        // Do one shallow pass to define all top-level functions in the module.
        for statement in &self.program.statements {
            match statement {
                AStatement::FunctionDeclaration(func) => {
                    self.gen_fn_sig(&func.signature);
                }
                AStatement::Impl(impl_) => {
                    for mem_fn in &impl_.member_fns {
                        self.gen_fn_sig(&mem_fn.signature);
                    }
                }
                _ => {}
            }
        }

        // Compile all the statements in the program.
        for statement in &self.program.statements {
            match statement {
                AStatement::FunctionDeclaration(func) => {
                    FnCodeGen::compile(
                        self.ctx,
                        self.builder,
                        self.fpm,
                        self.module,
                        self.type_store,
                        &mut self.type_converter,
                        &self.module_consts,
                        func,
                    )?;
                }
                AStatement::Impl(impl_) => {
                    for mem_fn in &impl_.member_fns {
                        FnCodeGen::compile(
                            self.ctx,
                            self.builder,
                            self.fpm,
                            self.module,
                            self.type_store,
                            &mut self.type_converter,
                            &self.module_consts,
                            mem_fn,
                        )?;
                    }
                }
                AStatement::StructTypeDeclaration(_) | AStatement::EnumTypeDeclaration(_) => {
                    // Nothing to do here because types are compiled only when they're used.
                }
                AStatement::ExternFns(_) => {
                    // Nothing to do here because extern functions are compiled in the call to
                    // `ProgramCodeGen::define_extern_fns` above.
                }
                AStatement::Consts(_) => {
                    // Nothing to do here because constants are compiled in the call to
                    // `ProgramCodeGen::define_consts` above.
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
    fn gen_fn_sig(&mut self, sig: &AFnSig) {
        // Define the function in the module using the fully-qualified function name.
        let fn_type = self.type_converter.get_fn_type(sig.type_key);
        let fn_val = self
            .module
            .add_function(sig.mangled_name.as_str(), fn_type, None);

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
            if let AStatement::ExternFns(fn_sigs) = statement {
                for fn_sig in fn_sigs {
                    let ll_fn_type = self.type_converter.get_fn_type(fn_sig.type_key);
                    self.module.add_function(
                        fn_sig.name.as_str(),
                        ll_fn_type,
                        Some(Linkage::External),
                    );
                }
            }
        }
    }

    /// Defines constants in the current module.
    fn define_consts(&mut self) {
        for statement in &self.program.statements {
            if let AStatement::Consts(consts) = statement {
                for const_decl in consts {
                    self.module_consts
                        .insert(const_decl.name.clone(), const_decl.clone());
                }
            }
        }
    }
}

/// Generates the program code for the given target. If there is no target, compiles the
/// program for the host system.
pub fn generate(
    analyzed_sources: Vec<ASource>,
    type_store: TypeStore,
    maybe_target_triple: Option<&String>,
    output_format: OutputFormat,
    output_path: &Path,
    optimize: bool,
) -> CompileResult<()> {
    let ctx = Context::create();
    let builder = ctx.create_builder();
    let module = ctx.create_module("main");

    // Initialize the target machine and set the target on the LLVM module.
    let target_triple = match maybe_target_triple {
        Some(target_triple) => {
            // TODO: We probably don't need to initialize all targets - just the one we're
            // compiling to.
            Target::initialize_all(&InitializationConfig::default());
            TargetTriple::create(target_triple)
        }

        None => {
            match Target::initialize_native(&InitializationConfig::default()) {
                Ok(_) => {}
                Err(msg) => {
                    return Err(CodeGenError::new(ErrorKind::TargetInitFailed, msg.as_str()))
                }
            };

            TargetMachine::get_default_triple()
        }
    };
    module.set_triple(&target_triple);

    // Set up function pass manager that performs LLVM IR optimization.
    let fpm = PassManager::create(&module);
    if optimize {
        fpm.add_instruction_combining_pass();
        fpm.add_reassociate_pass();
        fpm.add_gvn_pass();
        fpm.add_cfg_simplification_pass();
        fpm.add_basic_alias_analysis_pass();
        fpm.add_promote_memory_to_register_pass();
    }
    fpm.initialize();

    // Combine sources into one big source.
    let source = ASource {
        path: "main".to_string(), // TODO
        statements: analyzed_sources
            .into_iter()
            .flat_map(|s| s.statements)
            .collect(),
    };

    // Create the program code generator and generate the program.
    let mut codegen = ProgramCodeGen {
        ctx: &ctx,
        builder: &builder,
        fpm: &fpm,
        module: &module,
        program: &source,
        type_store: &type_store,
        type_converter: TypeConverter::new(&ctx, &type_store),
        module_consts: HashMap::new(),
    };
    codegen.gen_program()?;

    // Write output to file.
    match output_format {
        OutputFormat::LLVMIR => {
            if let Err(e) = codegen.module.print_to_file(output_path) {
                return Err(CodeGenError::new(
                    ErrorKind::WriteOutFailed,
                    e.to_string().as_str(),
                ));
            }
        }

        OutputFormat::LLVMBitcode => {
            codegen.module.write_bitcode_to_path(output_path);
        }

        OutputFormat::Object | OutputFormat::Assembly => {
            let target = Target::from_triple(&target_triple).unwrap();
            let target_machine = target
                .create_target_machine(
                    &target_triple,
                    &"",
                    &"",
                    OptimizationLevel::Aggressive,
                    RelocMode::Default,
                    CodeModel::Default,
                )
                .unwrap();
            let file_type = match output_format {
                OutputFormat::Assembly => FileType::Assembly,
                OutputFormat::Object => FileType::Object,
                _ => unreachable!(),
            };

            // TODO: Sometimes this call will cause a segfault when the module is not optimized.
            // I have no idea why, but it's bad!
            if let Err(msg) = target_machine.write_to_file(&module, file_type, output_path) {
                return Err(CodeGenError::new(
                    ErrorKind::WriteOutFailed,
                    msg.to_str().unwrap(),
                ));
            }
        }
    };

    Ok(())
}
