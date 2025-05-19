use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::codegen::error::{CodeGenError, CodeGenResult, ErrorKind};
use crate::codegen::module::gen_module;
use crate::mono_collector::MonoProg;
use crate::parser::{ModID, SrcInfo};
use flamer::flame;
use inkwell::passes::PassBuilderOptions;
use inkwell::targets::{
    CodeModel, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple,
};
use inkwell::OptimizationLevel;
use rayon::prelude::*;

/// Compiles a type-rich and semantically valid program to LLVM IR and/or bitcode.
pub struct ProgramCodeGen<'a> {
    src_info: &'a SrcInfo,
    prog: &'a MonoProg,
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

impl OutputFormat {
    pub fn intermediate_file_extension(&self) -> &'static str {
        match self {
            OutputFormat::LLVMBitcode => "bc",
            OutputFormat::LLVMIR => "ll",
            OutputFormat::Assembly => "s",
            OutputFormat::Executable | OutputFormat::Object => "o",
        }
    }

    pub fn file_extension(&self) -> &'static str {
        match self {
            OutputFormat::LLVMBitcode => "bc",
            OutputFormat::LLVMIR => "ll",
            OutputFormat::Assembly => "s",
            OutputFormat::Object => "o",
            OutputFormat::Executable => "",
        }
    }
}

impl<'a> ProgramCodeGen<'a> {
    /// Compiles the program to LLVM IR.
    #[flame]
    fn gen_program(&mut self) -> CodeGenResult<HashSet<ModID>> {
        let builtins_mod_id = self
            .src_info
            .mod_info
            .get_id_by_path("std/builtins")
            .unwrap();
        let mut mod_ids: HashSet<ModID> = HashSet::from([builtins_mod_id]);

        // Collect mod IDs from mono items.
        for (mod_id, items) in &self.prog.mono_items {
            if !items.is_empty() {
                mod_ids.insert(*mod_id);
            }
        }

        // Collect mod IDs from extern fns.
        for (mod_id, extern_fns) in &self.prog.extern_fns {
            if !extern_fns.is_empty() {
                mod_ids.insert(*mod_id);
            }
        }

        // Do module codegen in parallel.
        let errs: Vec<CodeGenError> = mod_ids
            .par_iter()
            .filter_map(
                |mod_id| match gen_module(&self.src_info, &self.prog, *mod_id) {
                    Ok(_) => None,
                    Err(err) => Some(err),
                },
            )
            .collect();

        match errs.is_empty() {
            true => Ok(mod_ids),
            // TODO: Potentially losing errors here.
            false => Err(errs.into_iter().next().unwrap()),
        }
    }
}

/// Returns an error if the target triple is invalid.
pub fn validate_target_triple(triple: &str) -> Result<(), String> {
    match Target::from_triple(&TargetTriple::create(triple)) {
        Ok(_) => Ok(()),
        Err(err) => Err(err.to_string()),
    }
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
    pub target_triple: Option<String>,
    pub output_format: OutputFormat,
    pub output_path: PathBuf,
    pub optimization_level: OptimizationLevel,
    pub reloc_mode: RelocMode,
    pub linker: Option<String>,
    pub linker_args: Vec<String>,
    pub emit_debug_info: bool,
    /// Whether to have LLVM verify each function in the resulting IR. This makes codegen at least
    /// twice as slow, so it should only be turned on for testing and debugging.
    pub verify: bool,
}

impl CodeGenConfig {
    /// Creates codegen config with default settings.
    pub fn new_default(output_path: PathBuf, output_format: OutputFormat) -> CodeGenConfig {
        CodeGenConfig {
            target_triple: None,
            output_format,
            output_path,
            optimization_level: OptimizationLevel::Default,
            reloc_mode: RelocMode::Default,
            linker: None,
            linker_args: vec![],
            emit_debug_info: false,
            verify: false,
        }
    }

    /// Creates codegen config with default settings for tests.
    #[cfg(test)]
    pub fn new_test_default(output_path: PathBuf, output_format: OutputFormat) -> CodeGenConfig {
        let mut cfg = CodeGenConfig::new_default(output_path, output_format);
        cfg.verify = true;
        cfg
    }

    pub fn optimization_pass_config(&self) -> (String, PassBuilderOptions) {
        let optimization_pass_pipeline = match self.optimization_level {
            OptimizationLevel::None => "default<O0>",
            OptimizationLevel::Less => "default<O1>",
            OptimizationLevel::Default => "default<O2>",
            OptimizationLevel::Aggressive => "default<O3>",
        };

        let opts = PassBuilderOptions::create();
        opts.set_verify_each(self.verify);
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
pub fn gen_program(src_info: &SrcInfo, prog: MonoProg) -> CodeGenResult<()> {
    // Create the program code generator and generate the program.
    let mut codegen = ProgramCodeGen {
        src_info,
        prog: &prog,
    };
    let mod_ids = codegen.gen_program()?;

    let ext = prog.config.output_format.intermediate_file_extension();
    let cwd = Path::new(".");
    let output_dir = prog.config.output_path.parent().unwrap_or(cwd);
    let mod_cache_dir = output_dir.join(".cache");
    let mut paths = vec![];

    // Collect output file paths in dependency order.
    for mod_path in src_info.mod_paths_in_order(prog.root_mod_id, mod_ids) {
        let output_file = mod_cache_dir.join(mod_path).with_extension(ext);
        paths.push(output_file);
    }
    paths.push(mod_cache_dir.join("std/builtins").with_extension(ext));

    let target_machine = init_target_machine(
        prog.config.target_triple.as_ref(),
        prog.config.optimization_level,
        prog.config.reloc_mode,
    )?;

    // Link output files together.
    link(
        &prog.config.linker,
        &prog.config.output_format,
        &target_machine.get_triple().to_string(),
        paths,
        &prog.config.output_path,
        &prog.config.linker_args,
    )
}

/// Invokes the system linker to link the given object files into an executable that is created
/// at the given output path.
#[flame]
fn link(
    linker: &Option<String>,
    output_format: &OutputFormat,
    target_triple: &str,
    obj_file_paths: Vec<PathBuf>,
    output_path: &Path,
    linker_args: &[String],
) -> Result<(), CodeGenError> {
    let mut extra_link_args = vec![];
    let linker_cmd = if let Some(linker) = linker {
        linker.as_str()
    } else {
        match output_format {
            OutputFormat::LLVMBitcode | OutputFormat::LLVMIR => {
                if !linker_args.contains(&"-S".to_string()) {
                    // Append -S to tell LLVM to output IR/bitcode instead of an object file or
                    // executable.
                    extra_link_args.push("-S".to_string());
                }
                "llvm-link"
            }
            OutputFormat::Assembly | OutputFormat::Object | OutputFormat::Executable => {
                // Try to determine the system linker based on the target platform.
                match target_triple.contains("windows") {
                    true => "link.exe",
                    false => "cc",
                }
            }
        }
    };

    // Assemble and execute the link command to link object files into an executable.
    let mut link_cmd = Command::new(linker_cmd);
    link_cmd
        .args(linker_args)
        .args(extra_link_args)
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
