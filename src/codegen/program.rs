use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use flamer::flame;
use inkwell::attributes::AttributeLoc;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::passes::PassBuilderOptions;
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple,
};
use inkwell::values::{BasicMetadataValueEnum, BasicValue};
use inkwell::OptimizationLevel;

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::ext::AExternFn;
use crate::analyzer::ast::func::AFn;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::type_store::{GetType, TypeKey, TypeStore};
use crate::codegen::convert::TypeConverter;
use crate::codegen::error::{CodeGenError, CodeGenResult, ErrorKind};
use crate::codegen::func::debug::new_di_ctx;
use crate::codegen::func::{gen_fn_sig, DICtx, FnCodeGen};
use crate::mono_collector::{MonoItem, MonoProg};
use crate::parser::{ModID, SrcInfo};

/// Compiles a type-rich and semantically valid program to LLVM IR and/or bitcode.
pub struct ProgramCodeGen<'a, 'ctx> {
    ctx: &'ctx Context,
    src_info: &'a SrcInfo,
    builder: &'a Builder<'ctx>,
    module: &'a Module<'ctx>,
    fns: &'a HashMap<TypeKey, AFn>,
    extern_fns: &'a HashMap<TypeKey, AExternFn>,
    nested_fns: &'a HashSet<TypeKey>,
    mono_items: &'a Vec<MonoItem>,
    maybe_main_fn_name: Option<String>,
    type_store: &'a TypeStore,
    type_converter: TypeConverter<'ctx>,
    mod_consts: HashMap<ModID, HashMap<String, AExpr>>,
    /// Whether to include debug info in the LLVM IR.
    emit_debug_info: bool,
}

/// The type of output file to generate.
#[derive(PartialEq, Clone, Copy)]
pub enum OutputFormat {
    LLVMBitcode,
    LLVMIR,
    Assembly,
    Object,
    Executable,
}

impl<'a, 'ctx> ProgramCodeGen<'a, 'ctx> {
    /// Compiles the program to LLVM IR.
    #[flame]
    fn gen_program(&mut self) -> CodeGenResult<()> {
        // Set debug info metadata.
        if self.emit_debug_info {
            let debug_metadata_version = self.ctx.i32_type().const_int(3, false);
            self.module.add_basic_value_flag(
                "Debug Info Version",
                inkwell::module::FlagBehavior::Warning,
                debug_metadata_version,
            );
        }

        // Generate extern functions.
        for extern_fn in self.extern_fns.values() {
            self.gen_extern_fn(extern_fn);
        }

        // Define functions.
        for (i, item) in self.mono_items.iter().enumerate() {
            // Skip the root mono item because it's meaningless.
            if i == 0 {
                continue;
            }

            self.type_converter
                .set_type_mapping(item.type_mappings.clone());
            let sig = self
                .type_converter
                .get_type(item.type_key)
                .to_fn_sig()
                .clone();
            let is_nested = self.nested_fns.contains(&sig.type_key);
            gen_fn_sig(
                self.ctx,
                self.module,
                &mut self.type_converter,
                &sig,
                is_nested,
            );
        }

        // Generate functions.
        let mut di_ctxs: HashMap<ModID, DICtx> = HashMap::new();
        for (i, item) in self.mono_items.iter().enumerate() {
            // Skip the root mono item because it's meaningless.
            if i == 0 {
                continue;
            }

            self.type_converter
                .set_type_mapping(item.type_mappings.clone());

            let typ = self.type_converter.get_type(item.type_key);
            match typ {
                AType::Function(fn_sig) => {
                    let func = self.fns.get(&fn_sig.type_key).unwrap();
                    let file_id = func.span.file_id;

                    let maybe_di_ctx = if self.emit_debug_info {
                        if let Some(di_ctx) = di_ctxs.get_mut(&file_id) {
                            Some(di_ctx)
                        } else {
                            let di_ctx = new_di_ctx(self.src_info, file_id, self.module);
                            di_ctxs.insert(file_id, di_ctx);
                            Some(di_ctxs.get_mut(&file_id).unwrap())
                        }
                    } else {
                        None
                    };

                    FnCodeGen::generate(
                        self.ctx,
                        self.src_info,
                        self.builder,
                        maybe_di_ctx,
                        self.module,
                        self.type_store,
                        &mut self.type_converter,
                        &self.nested_fns,
                        &self.mod_consts,
                        func,
                    )?;
                }

                other => {
                    panic!("unexpected statement {other}")
                }
            }
        }

        for di_ctx in di_ctxs.into_values() {
            di_ctx.di_builder.finalize();
        }

        // If a main function was defined, generate a wrapping main that calls it.
        // This is necessary because the defined main function will not have the name
        // "main", but rather something like "my_project/my_module/main.bl::main`,
        // so the linker won't locate it as the entrypoint. Generating our own
        // wrapping main also gives us the opportunity to initialize things at
        // runtime, like a GC.
        if let Some(main_fn_name) = &self.maybe_main_fn_name {
            let ll_main_fn = self.module.get_function(main_fn_name).unwrap();
            let ll_wrapper_fn =
                self.module
                    .add_function("main", self.ctx.void_type().fn_type(&[], false), None);
            let ll_entry_block = self.ctx.append_basic_block(ll_wrapper_fn, "entry");
            self.builder.position_at_end(ll_entry_block);
            self.builder.build_call(ll_main_fn, &[], "main").unwrap();
            self.builder.build_return(None).unwrap();
        }

        Ok(())
    }

    /// Generates an extern function. Extern functions are generated as two functions:
    /// 1. A function with a mangled name that calls 2 and returns its result.
    /// 2. A function with the original unmangled name that is defined without body
    ///    that will be linked externally by the linker.
    fn gen_extern_fn(&mut self, ext_fn: &AExternFn) {
        let fn_sig = &ext_fn.fn_sig;
        let link_name = match &ext_fn.maybe_link_name {
            Some(name) => name,
            None => &fn_sig.name,
        };

        // Generate the external function definition.
        let ll_fn_type = self.type_converter.get_fn_type(fn_sig.type_key);
        let ll_extern_fn =
            self.module
                .add_function(link_name.as_str(), ll_fn_type, Some(Linkage::External));

        // Generate the internal function that calls the external one. We'll tell
        // LLVM to always inline this function.
        let ll_internal_fn =
            self.module
                .add_function(fn_sig.mangled_name.as_str(), ll_fn_type, None);
        ll_internal_fn.add_attribute(
            AttributeLoc::Function,
            self.ctx.create_string_attribute("alwaysinline", ""),
        );

        let ll_entry_block = self.ctx.append_basic_block(ll_internal_fn, "entry");
        self.builder.position_at_end(ll_entry_block);
        let ll_args: Vec<BasicMetadataValueEnum> = ll_internal_fn
            .get_params()
            .iter()
            .map(|param| param.as_basic_value_enum().into())
            .collect();
        let ll_ret_val = self
            .builder
            .build_call(ll_extern_fn, ll_args.as_slice(), "extern_call")
            .unwrap()
            .try_as_basic_value()
            .left();
        let ll_ret_val: Option<&dyn BasicValue> = match ll_ret_val.as_ref() {
            Some(ret_val) => Some(ret_val),
            None => None,
        };
        self.builder.build_return(ll_ret_val).unwrap();
    }
}

/// Initializes a target machine for the host system with default optimization level
/// and reloc mode.
pub fn init_default_host_target() -> Result<TargetMachine, CodeGenError> {
    init_target_machine(None, OptimizationLevel::Default, RelocMode::Default)
}

/// Initialize the target machine from the given triple, or from information gathered from the host
/// platform if the given target is None.
pub fn init_target_machine(
    maybe_target_triple: Option<&String>,
    optimization_level: OptimizationLevel,
    reloc_mode: RelocMode,
) -> Result<TargetMachine, CodeGenError> {
    // Create a target triple from either the given triple or the host system.
    let (target_triple, cpu_name, cpu_features) = match maybe_target_triple {
        Some(triple) => {
            // TODO: We probably don't need to initialize all targets - just the one we're
            // compiling to.
            Target::initialize_all(&InitializationConfig::default());
            let target_triple = TargetTriple::create(triple);
            (target_triple, "".to_string(), "".to_string())
        }

        None => {
            if let Err(msg) = Target::initialize_native(&InitializationConfig::default()) {
                return Err(CodeGenError::new(ErrorKind::TargetInitFailed, msg.as_str()));
            };

            (
                TargetMachine::get_default_triple(),
                TargetMachine::get_host_cpu_name().to_string(),
                TargetMachine::get_host_cpu_features().to_string(),
            )
        }
    };

    // Create a target.
    let target = match Target::from_triple(&target_triple) {
        Ok(target) => target,
        Err(msg) => {
            return Err(CodeGenError::new(
                ErrorKind::TargetInitFailed,
                format!("failed to create target triple: {}", msg).as_str(),
            ))
        }
    };

    // Create a target machine.
    match target.create_target_machine(
        &target_triple,
        &cpu_name,
        &cpu_features,
        optimization_level,
        reloc_mode,
        CodeModel::Default,
    ) {
        None => Err(CodeGenError::new(
            ErrorKind::TargetInitFailed,
            format!(
                "failed to initialize machine for {}",
                target_triple.to_string()
            )
            .as_str(),
        )),
        Some(machine) => Ok(machine),
    }
}

/// Contains configuration that dictates how code gets generated by the backend.
pub struct CodeGenConfig {
    pub target_machine: TargetMachine,
    pub output_format: OutputFormat,
    pub output_path: PathBuf,
    pub optimization_level: OptimizationLevel,
    pub linker: Option<String>,
    pub linker_args: Vec<String>,
    pub emit_debug_info: bool,
}

impl CodeGenConfig {
    /// Creates codegen config with default settings.
    pub fn new_default(
        target_machine: TargetMachine,
        output_path: PathBuf,
        output_format: OutputFormat,
    ) -> CodeGenConfig {
        CodeGenConfig {
            target_machine,
            output_format,
            output_path,
            optimization_level: OptimizationLevel::Default,
            linker: None,
            linker_args: vec![],
            emit_debug_info: false,
        }
    }

    /// Creates codegen config with default settings for tests.
    #[cfg(test)]
    pub fn new_test_default(
        target_machine: TargetMachine,
        output_path: PathBuf,
        output_format: OutputFormat,
    ) -> CodeGenConfig {
        CodeGenConfig {
            target_machine,
            output_format,
            output_path,
            optimization_level: OptimizationLevel::Default,
            linker: None,
            linker_args: vec![],
            emit_debug_info: false, // TODO: Set this to true when it's not broken.
        }
    }

    pub fn optimization_pass_config(&self) -> (String, PassBuilderOptions) {
        let optimization_pass_pipeline = match self.optimization_level {
            OptimizationLevel::None => "default<O0>",
            OptimizationLevel::Less => "default<O1>",
            OptimizationLevel::Default => "default<O2>",
            OptimizationLevel::Aggressive => "default<O3>",
        };

        let opts = PassBuilderOptions::create();
        opts.set_verify_each(true);
        opts.set_debug_logging(false);
        opts.set_loop_interleaving(true);
        opts.set_loop_vectorization(true);
        opts.set_loop_slp_vectorization(true);
        opts.set_loop_unrolling(true);
        opts.set_forget_all_scev_in_loop_unroll(true);
        opts.set_licm_mssa_opt_cap(1);
        opts.set_licm_mssa_no_acc_for_promotion_cap(10);
        opts.set_call_graph_profile(true);
        opts.set_merge_functions(true);

        (optimization_pass_pipeline.to_string(), opts)
    }
}

/// Generates the program code for the given target. If there is no target, compiles the
/// program for the host system.
#[flame]
pub fn generate(src_info: &SrcInfo, prog: MonoProg) -> CodeGenResult<()> {
    let ctx = Context::create();
    let builder = ctx.create_builder();
    let module = ctx.create_module("main");

    // Set the module triple and data layout based on the target machine.
    let target_data = prog.config.target_machine.get_target_data();
    let data_layout = target_data.get_data_layout();
    module.set_triple(&prog.config.target_machine.get_triple());
    module.set_data_layout(&data_layout);

    // Create the program code generator and generate the program.
    let mut codegen = ProgramCodeGen {
        ctx: &ctx,
        src_info,
        builder: &builder,
        module: &module,
        fns: &prog.fns,
        extern_fns: &prog.extern_fns,
        nested_fns: &prog.nested_fns,
        mono_items: &prog.mono_items,
        maybe_main_fn_name: prog.maybe_main_fn_mangled_name,
        type_store: &prog.type_store,
        type_converter: TypeConverter::new(&ctx, &prog.type_store, &prog.config.target_machine),
        mod_consts: prog.mod_consts,
        emit_debug_info: prog.config.emit_debug_info,
    };
    codegen.gen_program()?;

    // Run optimization passes.
    optimize(codegen.module, &prog.config)?;

    // Write generated code to a file.
    emit_to_file(codegen.module, &prog.config)?;

    Ok(())
}

/// Runs optimization passes on the LLVM module.
#[flame]
fn optimize(module: &Module, config: &CodeGenConfig) -> CodeGenResult<()> {
    let (opt_pipeline, opts) = config.optimization_pass_config();
    match module.run_passes(&opt_pipeline, &config.target_machine, opts) {
        Ok(_) => Ok(()),
        Err(err) => Err(CodeGenError::new(
            ErrorKind::OptimizationFailed,
            &err.to_string(),
        )),
    }
}

/// Invokes the system linker to link the given object files into an executable that is created
/// at the given output path.
#[flame]
fn link(
    linker: &Option<String>,
    target_triple: TargetTriple,
    obj_file_paths: Vec<&Path>,
    output_path: &Path,
    linker_args: &Vec<String>,
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

    // Convert the command to a str so we can log it, if necessary.
    let raw_cmd = format!(
        "{} {}",
        linker_cmd,
        link_cmd
            .get_args()
            .map(|a| a.to_string_lossy())
            .collect::<Vec<_>>()
            .join(" "),
    );

    match link_cmd.output() {
        Ok(output) => match output.status.success() {
            true => {
                // Log any warnings that occurred.
                if !output.stderr.is_empty() {
                    eprintln!("{}", String::from_utf8(output.stderr.clone()).unwrap());
                }
                Ok(())
            }

            false => Err(CodeGenError::new(
                ErrorKind::LinkingFailed,
                format!(
                    "\"{}\": {}",
                    raw_cmd,
                    String::from_utf8(output.stderr)
                        .unwrap_or("".to_string())
                        .as_str()
                )
                .as_str(),
            )),
        },

        Err(err) => Err(CodeGenError::new(
            ErrorKind::LinkingFailed,
            format!("failed to invoke linker \"{}\"\n{}", raw_cmd, err).as_str(),
        )),
    }
}

/// Writes compilation output to a file.
#[flame]
fn emit_to_file(module: &Module, config: &CodeGenConfig) -> CodeGenResult<()> {
    // Create the output directory if it does not yet exist.
    if let Some(parent_dir) = config.output_path.parent() {
        if let Err(e) = fs::create_dir_all(parent_dir) {
            return Err(CodeGenError::new(
                ErrorKind::WriteOutFailed,
                format!(
                    "failed to create output directory {}: {}",
                    parent_dir.display(),
                    e
                )
                .as_str(),
            ));
        }
    }

    // Write output to file.
    match config.output_format {
        OutputFormat::LLVMIR => {
            if let Err(e) = module.print_to_file(&config.output_path) {
                return Err(CodeGenError::new(
                    ErrorKind::WriteOutFailed,
                    e.to_string().as_str(),
                ));
            }

            Ok(())
        }

        OutputFormat::LLVMBitcode => {
            module.write_bitcode_to_path(&config.output_path);
            Ok(())
        }

        OutputFormat::Executable => {
            // Write temporary object file.
            let obj_file_path = config.output_path.with_extension("o");
            if let Err(msg) = config.target_machine.write_to_file(
                &module,
                FileType::Object,
                obj_file_path.as_path(),
            ) {
                return Err(CodeGenError::new(
                    ErrorKind::WriteOutFailed,
                    msg.to_str().unwrap(),
                ));
            }

            // To generate an executable, we need to invoke the system linker to link object
            // files.
            link(
                &config.linker,
                module.get_triple(),
                vec![obj_file_path.as_path()],
                &config.output_path,
                &config.linker_args,
            )?;

            Ok(())
        }

        OutputFormat::Object | OutputFormat::Assembly => {
            let file_type = match config.output_format {
                OutputFormat::Assembly => FileType::Assembly,
                OutputFormat::Object => FileType::Object,
                _ => unreachable!(),
            };

            match config
                .target_machine
                .write_to_file(&module, file_type, &config.output_path)
            {
                Ok(_) => Ok(()),
                Err(msg) => Err(CodeGenError::new(
                    ErrorKind::WriteOutFailed,
                    msg.to_str().unwrap(),
                )),
            }
        }
    }
}
