use std::collections::{HashMap, HashSet};
use std::fs::remove_file;
use std::path::Path;
use std::process::Command;

use flamer::flame;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::passes::PassManager;
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetTriple,
};
use inkwell::values::FunctionValue;
use inkwell::OptimizationLevel;
use target_lexicon::Triple;

use crate::analyzer::analyze::ProgramAnalysis;
use crate::analyzer::ast::func::AFn;
use crate::analyzer::ast::module::AModule;
use crate::analyzer::ast::r#const::AConst;
use crate::analyzer::ast::statement::AStatement;
use crate::analyzer::prog_context::Monomorphization;
use crate::analyzer::type_store::{TypeKey, TypeStore};
use crate::codegen::convert::TypeConverter;
use crate::codegen::error::{CodeGenError, CompileResult, ErrorKind};
use crate::codegen::func;
use crate::codegen::func::FnCodeGen;
use crate::fmt::vec_to_string;

/// Compiles a type-rich and semantically valid program to LLVM IR and/or bitcode.
pub struct ProgramCodeGen<'a, 'ctx> {
    ctx: &'ctx Context,
    builder: &'a Builder<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    module: &'a Module<'ctx>,
    program: &'a AModule,
    monomorphized_types: &'a HashMap<TypeKey, HashSet<Monomorphization>>,
    type_store: &'a TypeStore,
    type_converter: TypeConverter<'ctx>,
    module_consts: HashMap<String, AConst>,
}

/// The type of output file to generate.
#[derive(PartialEq)]
pub enum OutputFormat {
    LLVMBitcode,
    LLVMIR,
    Assembly,
    Object,
    Executable,
}

impl<'a, 'ctx> ProgramCodeGen<'a, 'ctx> {
    /// Compiles the program to LLVM IR.
    fn gen_program(&mut self) -> CompileResult<()> {
        // Define top-level functions and constants from the program in the LLVM module.
        self.declare_fns_and_consts();

        // Generate all the statements in the program.
        for statement in &self.program.statements {
            match statement {
                AStatement::FunctionDeclaration(func) => {
                    self.gen_fn(func)?;
                }
                AStatement::Impl(impl_) => {
                    for mem_fn in &impl_.member_fns {
                        self.gen_fn(mem_fn)?;
                    }
                }
                AStatement::StructTypeDeclaration(_) | AStatement::EnumTypeDeclaration(_) => {
                    // Nothing to do here because types are compiled only when they're used.
                }
                AStatement::ExternFn(_) => {
                    // Nothing to do here because extern functions are compiled in the call to
                    // `ProgramCodeGen::declare_fns_and_consts`.
                }
                AStatement::Const(_) => {
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

    /// Generates code for the given function.
    fn gen_fn(&mut self, func: &AFn) -> CompileResult<()> {
        if !func.signature.is_parameterized() {
            FnCodeGen::generate(
                self.ctx,
                self.builder,
                self.fpm,
                self.module,
                self.type_store,
                &mut self.type_converter,
                &self.module_consts,
                func,
            )?;
            return Ok(());
        }

        // This is a generic function, so we need to generate
        // code for all its monomorphizations.
        let mappings = self.resolve_monomorphizations(func.signature.type_key);
        for mapping in mappings {
            let mut new_func = func.clone();
            let mut replacement_tks = vec![];
            for param in &new_func.signature.params.as_ref().unwrap().params {
                replacement_tks.push(mapping.get(&param.generic_type_key).unwrap());
            }

            new_func.signature.mangled_name +=
                format!("[{}]", vec_to_string(&replacement_tks, ",")).as_str();

            self.type_converter.push_type_mapping(mapping);

            FnCodeGen::generate(
                self.ctx,
                self.builder,
                self.fpm,
                self.module,
                self.type_store,
                &mut self.type_converter,
                &self.module_consts,
                &new_func,
            )?;

            self.type_converter.pop_type_mapping();
        }

        Ok(())
    }

    fn resolve_monomorphizations(&self, type_key: TypeKey) -> Vec<HashMap<TypeKey, TypeKey>> {
        let monomorphs = match self.monomorphized_types.get(&type_key) {
            Some(monomorphs) => monomorphs,
            None => {
                return vec![];
            }
        };

        let mut all_mappings = vec![];
        for mono in monomorphs {
            all_mappings.extend(self.resolve_monomorphization(mono));
        }

        all_mappings
    }

    fn resolve_monomorphization(&self, mono: &Monomorphization) -> Vec<HashMap<TypeKey, TypeKey>> {
        // Create a type mapping from the monomorphization.
        let mut type_mapping: HashMap<TypeKey, TypeKey> = HashMap::new();
        for replaced_param in &mono.replaced_params {
            type_mapping.insert(
                replaced_param.param_type_key,
                replaced_param.replacement_type_key,
            );
        }

        // Find the keys of all types that are still mapped to generic types.
        let mut unresolved_tks = vec![];
        for (k, v) in &type_mapping {
            if self.type_store.must_get(*v).is_generic() {
                unresolved_tks.push(*k);
            }
        }

        // If no types are mapped to generic types, we're done.
        if unresolved_tks.is_empty() {
            return vec![type_mapping];
        }

        // Find the polymorphic parent type keys for all unresolved (generic) types.
        let mut poly_tks = HashSet::new();
        for unresolved_tk in &unresolved_tks {
            let generic_type = self
                .type_store
                .must_get(*type_mapping.get(unresolved_tk).unwrap())
                .to_generic_type();
            poly_tks.insert(generic_type.poly_type_key);
        }

        let mut resolved_mappings = vec![];
        for poly_tk in poly_tks {
            let monos = self.resolve_monomorphizations(poly_tk);
            for mapping in monos {
                let mut new_mapping = type_mapping.clone();
                for unresolved_tk in &unresolved_tks {
                    if let Some(replacement_tk) =
                        mapping.get(type_mapping.get(&unresolved_tk).unwrap())
                    {
                        new_mapping.insert(*unresolved_tk, *replacement_tk);
                    }
                }

                // TODO: need to make permutations.
                resolved_mappings.push(new_mapping);
            }
        }

        resolved_mappings
    }

    /// Declares the following inside the LLVM module (without assigning values)
    /// - functions
    /// - extern functions (to be linked by the linker)
    /// - constants
    fn declare_fns_and_consts(&mut self) {
        for statement in &self.program.statements {
            match statement {
                AStatement::Const(const_decl) => {
                    self.module_consts
                        .insert(const_decl.name.clone(), const_decl.clone());
                }

                AStatement::ExternFn(fn_sig) => {
                    let ll_fn_type = self.type_converter.get_fn_type(fn_sig.type_key);
                    self.module.add_function(
                        fn_sig.name.as_str(),
                        ll_fn_type,
                        Some(Linkage::External),
                    );
                }

                AStatement::FunctionDeclaration(func) if !func.signature.is_parameterized() => {
                    func::gen_fn_sig(
                        self.ctx,
                        self.module,
                        &mut self.type_converter,
                        &func.signature,
                    );
                }

                AStatement::Impl(impl_) => {
                    for mem_fn in &impl_.member_fns {
                        if !mem_fn.signature.is_parameterized() {
                            func::gen_fn_sig(
                                self.ctx,
                                self.module,
                                &mut self.type_converter,
                                &mem_fn.signature,
                            );
                        }
                    }
                }

                _ => {}
            };
        }

        // Generate function signatures for monomorphized functions.
        for poly_tk in self.monomorphized_types.keys() {
            let poly_type = self.type_store.must_get(*poly_tk);
            if !poly_type.is_fn() {
                continue;
            }

            let mappings = self.resolve_monomorphizations(*poly_tk);
            for mapping in mappings {
                let mut mono_fn_sig = poly_type.to_fn_sig().clone();
                let mut replacement_tks = vec![];
                for param in &mono_fn_sig.params.as_ref().unwrap().params {
                    replacement_tks.push(mapping.get(&param.generic_type_key).unwrap());
                }

                mono_fn_sig.mangled_name +=
                    format!("[{}]", vec_to_string(&replacement_tks, ",")).as_str();
                mono_fn_sig.params = None;

                self.type_converter.push_type_mapping(mapping);

                func::gen_fn_sig(
                    self.ctx,
                    self.module,
                    &mut self.type_converter,
                    &mono_fn_sig,
                );

                self.type_converter.pop_type_mapping();
            }
        }
    }
}

/// Initialize the target machine from the given triple (or from information gathered from the host
/// platform if the given target is None.
pub fn init_target(maybe_target_triple: Option<&String>) -> Result<TargetTriple, CodeGenError> {
    match maybe_target_triple {
        Some(target_triple) => {
            // TODO: We probably don't need to initialize all targets - just the one we're
            // compiling to.
            Target::initialize_all(&InitializationConfig::default());
            Ok(TargetTriple::create(target_triple))
        }

        None => {
            match Target::initialize_native(&InitializationConfig::default()) {
                Ok(_) => {}
                Err(msg) => {
                    return Err(CodeGenError::new(ErrorKind::TargetInitFailed, msg.as_str()))
                }
            };

            Ok(TargetTriple::create(Triple::host().to_string().as_str()))
        }
    }
}

/// Generates the program code for the given target. If there is no target, compiles the
/// program for the host system.
#[flame]
pub fn generate(
    program_analysis: ProgramAnalysis,
    target_triple: &TargetTriple,
    output_format: OutputFormat,
    output_path: &Path,
    optimize: bool,
    linker: Option<&String>,
    linker_args: Vec<&String>,
) -> CompileResult<()> {
    let ctx = Context::create();
    let builder = ctx.create_builder();
    let module = ctx.create_module("main");

    // Initialize the target machine and set the target on the LLVM module.
    module.set_triple(target_triple);

    // Set data layout.
    let data_layout = module
        .create_jit_execution_engine(OptimizationLevel::None)
        .unwrap()
        .get_target_data()
        .get_data_layout();
    module.set_data_layout(&data_layout);

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
    let a_module = AModule {
        path: "main".to_string(), // TODO
        statements: program_analysis
            .analyzed_modules
            .into_iter()
            .flat_map(|m| m.module.statements)
            .collect(),
    };

    // Create the program code generator and generate the program.
    let mut codegen = ProgramCodeGen {
        ctx: &ctx,
        builder: &builder,
        fpm: &fpm,
        module: &module,
        program: &a_module,
        monomorphized_types: &program_analysis.monomorphized_types,
        type_store: &program_analysis.type_store,
        type_converter: TypeConverter::new(&ctx, &program_analysis.type_store),
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

        OutputFormat::Object | OutputFormat::Assembly | OutputFormat::Executable => {
            let target = Target::from_triple(&target_triple).unwrap();
            let target_machine = target
                .create_target_machine(
                    &target_triple,
                    &"",
                    &"",
                    OptimizationLevel::Default,
                    RelocMode::Default,
                    CodeModel::Default,
                )
                .unwrap();
            let file_type = match output_format {
                OutputFormat::Assembly => FileType::Assembly,
                OutputFormat::Object | OutputFormat::Executable => FileType::Object,
                _ => unreachable!(),
            };

            if output_format == OutputFormat::Executable {
                // Write temporary object file.
                let obj_file_path = output_path.with_extension("o");
                {
                    if let Err(msg) =
                        target_machine.write_to_file(&module, file_type, obj_file_path.as_path())
                    {
                        return Err(CodeGenError::new(
                            ErrorKind::WriteOutFailed,
                            msg.to_str().unwrap(),
                        ));
                    }
                }

                // To generate an executable, we need to invoke the system linker to link object
                // files.
                let result = link(
                    linker,
                    module.get_triple(),
                    vec![obj_file_path.as_path()],
                    output_path,
                    linker_args,
                );

                // Try to clean up object files before returning.
                _ = remove_file(obj_file_path);
                return result;
            }

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

/// Invokes the system linker to link the given object files into an executable that is created
/// at the given output path.
#[flame]
fn link(
    linker: Option<&String>,
    target_triple: TargetTriple,
    obj_file_paths: Vec<&Path>,
    output_path: &Path,
    linker_args: Vec<&String>,
) -> Result<(), CodeGenError> {
    // Try to determine the system linker based on the target platform.
    let linker_cmd = if let Some(linker) = linker {
        linker
    } else if target_triple.to_string().contains("windows") {
        "link.exe"
    } else {
        "cc"
    };

    // Assemble and execute the link command to link object files into an executable.
    let mut link_cmd = Command::new(linker_cmd);
    link_cmd
        .args(linker_args)
        .args(["-o", output_path.to_str().unwrap()])
        .args(obj_file_paths);
    match link_cmd.output() {
        Ok(output) => match output.status.success() {
            true => Ok(()),
            false => Err(CodeGenError::new(
                ErrorKind::LinkingFailed,
                String::from_utf8(output.stderr)
                    .unwrap_or("".to_string())
                    .as_str(),
            )),
        },

        Err(err) => Err(CodeGenError::new(
            ErrorKind::LinkingFailed,
            format!(r#"failed to invoke linker "{}"\n{}"#, linker_cmd, err).as_str(),
        )),
    }
}
