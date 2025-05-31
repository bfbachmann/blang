use std::fmt::{Display, Formatter};
use std::fs::File;
use std::io::prelude::*;
use std::os::unix::prelude::CommandExt;
use std::path::{Path, PathBuf};
use std::process;
use std::time::Instant;

use clap::{arg, Arg, ArgAction, Command};
use flamer::flame;
use inkwell::targets::RelocMode;
use inkwell::OptimizationLevel;

use crate::analyzer::analyze::{analyze_modules, ProgramAnalysis};
use crate::codegen::error::CodeGenError;
use crate::codegen::program::{gen_program, validate_target_triple, CodeGenConfig, OutputFormat};
use crate::fmt::{display_msg, format_duration};
use crate::lexer::pos::Locatable;
use crate::mono_collector::mono_prog;
use crate::parser::{parse_mods, SrcInfo};

mod codegen;
#[macro_use]
mod fmt;
mod analyzer;
mod lexer;
mod mono_collector;
mod parser;
mod util;

fn main() {
    // Define the root command.
    let cmd = Command::new("blang")
        .version(env!("CARGO_PKG_VERSION"))
        .author("Bruno Bachmann")
        .about("The Blang programming language.")
        .subcommand_required(true)
        .arg_required_else_help(true)
        .arg(
            arg!(--time "Dump compile time information as HTML")
                .required(false)
                .action(ArgAction::SetTrue),
        );

    // Add the "build" subcommand for compiling.
    let cmd = cmd.subcommand(
        Command::new("build")
            .about("Compile Blang source code")
            .arg(
                arg!([TARGET_MODULE] "The module to compile")
                    .required(false)
                    .default_value("main"),
            )
            .arg(
                arg!(-O --"optimization-level" <OPT_LEVEL> "Optimization level")
                    .required(false)
                    .value_parser(["default", "none", "less", "aggressive"]),
            )
            .arg(
                arg!(-r --"reloc-mode" <RELOC_MODE> "Relocation mode")
                    .required(false)
                    .value_parser(["default", "pic", "dynamic-no-pic", "static.rs"]),
            )
            .arg(
                arg!(-q --quiet ... "Don't print log messages")
                    .required(false)
                    .action(ArgAction::SetTrue),
            )
            .arg(
                arg!(-d --debug "Generate source-level debug information")
                    .required(false)
                    .action(ArgAction::SetTrue),
            )
            .arg(arg!(-t --target <TARGET> "Generate code for the given target").required(false))
            .arg(
                arg!(-f --format <FORMAT> "Output file format")
                    .required(false)
                    .value_parser(["exe", "ir", "bc", "obj", "asm"]),
            )
            .arg(arg!(-o --out <FILE> "Write output to <FILE>").required(false))
            .arg(arg!(-l --linker <LINKER> "Linker to use").required(false))
            .arg(
                Arg::new("linker-flag")
                    .num_args(1..)
                    .value_delimiter(' ')
                    .short('L')
                    .required(false)
                    .allow_hyphen_values(true),
            ),
    );

    // Add the "check" subcommand for performing static.rs analysis.
    let cmd = cmd.subcommand(
        Command::new("check")
            .about("Perform static analysis only")
            .arg(
                arg!([TARGET_MODULE] "The module to check")
                    .required(false)
                    .default_value("main"),
            )
            .arg(arg!(-d --dump <DUMP_PATH> "Dump the analyzed AST to a file").required(false)),
    );

    // Add the "run" subcommand for building and running a binary.
    let cmd = cmd.subcommand(
        Command::new("run").about("Run Blang source code").arg(
            arg!([TARGET_MODULE] "The module to run")
                .required(false)
                .default_value("main"),
        ),
    );

    let matches = cmd.get_matches();

    // Handle the command.
    match matches.subcommand() {
        Some(("build", sub_matches)) => match sub_matches.get_one::<String>("TARGET_MODULE") {
            Some(target_mod) => {
                let target_triple = sub_matches.get_one::<String>("target").cloned();
                if let Some(triple) = &target_triple {
                    if let Err(err) = validate_target_triple(triple) {
                        eprintln!("{}", err);
                    }
                }

                let optimization_level = match sub_matches.get_one::<String>("optimization-level") {
                    Some(level) => match level.as_str() {
                        "default" => OptimizationLevel::Default,
                        "none" => OptimizationLevel::None,
                        "less" => OptimizationLevel::Less,
                        "aggressive" => OptimizationLevel::Aggressive,
                        _ => unreachable!(),
                    },

                    None => OptimizationLevel::Default,
                };

                let reloc_mode = match sub_matches.get_one::<String>("reloc-mode") {
                    Some(mode) => match mode.as_str() {
                        "default" => RelocMode::Default,
                        "pic" => RelocMode::PIC,
                        "dynamic-no-pic" => RelocMode::DynamicNoPic,
                        "static.rs" => RelocMode::Static,
                        _ => unreachable!(),
                    },

                    None => RelocMode::Default,
                };

                let dst_path = sub_matches.get_one::<String>("out");

                let output_format = match sub_matches.get_one::<String>("format") {
                    // If an output format was explicitly set, use that.
                    Some(output_format) => match output_format.as_str() {
                        "obj" => OutputFormat::Object,
                        "ir" => OutputFormat::LLVMIR,
                        "bc" => OutputFormat::LLVMBitcode,
                        "asm" => OutputFormat::Assembly,
                        "exe" => OutputFormat::Executable,
                        _ => unreachable!(),
                    },

                    // If no output format was set, try to determine the output format based on the
                    // destination file extension. If there is no dest file, just default to executable
                    // output format.
                    None => match dst_path {
                        Some(path) => match Path::new(path).extension() {
                            Some(ext) => match ext.to_str().unwrap().to_lowercase().as_str() {
                                "o" => OutputFormat::Object,
                                "ll" => OutputFormat::LLVMIR,
                                "bc" => OutputFormat::LLVMBitcode,
                                "s" | "asm" => OutputFormat::Assembly,
                                _ => OutputFormat::Executable,
                            },

                            None => OutputFormat::Executable,
                        },

                        None => OutputFormat::Executable,
                    },
                };

                let output_path = match dst_path {
                    Some(path) => PathBuf::from(path),
                    None => {
                        // If no output path was specified, just use the default generated from the
                        // source file path.
                        let src = Path::new(target_mod);
                        default_output_path(src, output_format)
                    }
                };

                let quiet = sub_matches.get_flag("quiet");
                let debug = sub_matches.get_flag("debug");

                let linker = sub_matches
                    .get_one::<String>("linker")
                    .map(|l| l.to_owned());

                let linker_args = sub_matches
                    .get_many::<String>("linker-flag")
                    .unwrap_or_default()
                    .cloned()
                    .collect();

                let codegen_config = CodeGenConfig {
                    target_triple,
                    output_path,
                    output_format,
                    optimization_level,
                    reloc_mode,
                    linker,
                    linker_args,
                    emit_debug_info: debug,
                    verify: false,
                };

                if let Err(e) = build(target_mod, quiet, codegen_config) {
                    fatalln!("{}", e);
                }
            }
            _ => fatalln!("expected source path"),
        },

        Some(("check", sub_matches)) => match sub_matches.get_one::<String>("TARGET_MODULE") {
            Some(target_mod) => {
                let maybe_dump_path = sub_matches.get_one::<String>("dump");
                let config = CodeGenConfig::new_default(PathBuf::new(), OutputFormat::LLVMIR);

                if let Err(e) = analyze(target_mod, maybe_dump_path, config) {
                    fatalln!("{}", e);
                };
            }
            _ => fatalln!("expected source path"),
        },

        Some(("run", sub_matches)) => match sub_matches.get_one::<String>("TARGET_MODULE") {
            Some(target_mod) => {
                let output_path =
                    default_output_path(Path::new(target_mod), OutputFormat::Executable);
                let config = CodeGenConfig::new_default(output_path, OutputFormat::Executable);

                run(target_mod, config);
            }
            _ => fatalln!("expected source path"),
        },

        _ => unreachable!("no subcommand"),
    };

    // Dump compiler performance/timing graph for debugging.
    if matches.get_one::<bool>("time").is_some() {
        flame::dump_html(&mut File::create("compile-time.html").unwrap()).unwrap();
    };
}

#[derive(Debug)]
enum AnalyzeProgError {
    ParsingFailed(String),
    ModNotFound(String),
    NoSourceFiles(String),
    AnalysisFailed(String),
    WriteOutFailed(String),
}

impl Display for AnalyzeProgError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            AnalyzeProgError::ParsingFailed(s) => s,
            AnalyzeProgError::ModNotFound(s) => s,
            AnalyzeProgError::NoSourceFiles(s) => s,
            AnalyzeProgError::AnalysisFailed(s) => s,
            AnalyzeProgError::WriteOutFailed(s) => s,
        };

        write!(f, "{}", s)
    }
}

/// Performs static.rs analysis on the source code starting at the given module path. Returns the
/// results of analysis, or an error message.
#[flame]
fn analyze(
    target_mod_path: &str,
    maybe_dump_path: Option<&String>,
    config: CodeGenConfig,
) -> Result<(SrcInfo, ProgramAnalysis), AnalyzeProgError> {
    // Parse all targeted source files.
    let (src_info, errs) = parse_mods(target_mod_path);

    if !errs.is_empty() {
        for err in &errs {
            match src_info.file_info.try_get_file_path_by_id(err.span.file_id) {
                Some(_) => {
                    display_msg(
                        &src_info,
                        &err.message,
                        None,
                        None,
                        &err.span,
                        false,
                        &vec![],
                    );
                }
                None => {
                    eprintln!("{}", err.message);
                }
            };
        }

        return Err(AnalyzeProgError::ParsingFailed(format!(
            "parsing failed with {} error(s)",
            errs.len()
        )));
    }

    if src_info.mod_info.is_empty() {
        return Err(AnalyzeProgError::NoSourceFiles(format!(
            r#"no source files found in "{}""#,
            target_mod_path
        )));
    }

    if src_info.mod_info.get_id_by_path(target_mod_path).is_none() {
        return Err(AnalyzeProgError::ModNotFound(format!(
            r#"module "{}" not found"#,
            target_mod_path
        )));
    }

    // Analyze the program.
    let analysis = analyze_modules(&src_info, target_mod_path, config);

    // Print warnings.
    let mut warn_count = 0;
    for module in analysis.analyzed_mods.values() {
        warn_count += module.warnings.len();
        for warn in &module.warnings {
            display_msg(
                &src_info,
                &warn.message,
                None,
                None,
                &warn.span,
                true,
                &vec![],
            );
        }
    }

    // Print errors.
    let mut err_count = 0;
    for module in analysis.analyzed_mods.values() {
        err_count += module.errors.len();
        for err in &module.errors {
            display_msg(
                &src_info,
                &err.message,
                err.detail.as_ref(),
                err.help.as_ref(),
                &err.span,
                false,
                &err.notes,
            );
        }
    }

    // Die if analysis failed.
    if err_count > 0 {
        return Err(AnalyzeProgError::AnalysisFailed(format!(
            "analysis failed with {err_count} error(s); {warn_count} warning(s)"
        )));
    }

    // Dump the AST to a file, if necessary.
    if let Some(dump_path) = maybe_dump_path {
        let dst = Path::new(dump_path.as_str());
        let mut dst_file = match File::create(dst) {
            Err(err) => {
                return Err(AnalyzeProgError::WriteOutFailed(format!(
                    "error opening file {}: {}",
                    dst.to_str().unwrap_or_default(),
                    err
                )));
            }
            Ok(result) => result,
        };

        if let Err(err) = write!(dst_file, "{:#?}", analysis.analyzed_mods) {
            return Err(AnalyzeProgError::WriteOutFailed(format!(
                "error writing AST to file {}: {}",
                dst.to_str().unwrap_or_default(),
                err
            )));
        }
    }

    Ok((src_info, analysis))
}

#[derive(Debug)]
enum CompileProgError {
    AnalysisFailed(AnalyzeProgError),
    MissingMain,
    CodeGenFailed(CodeGenError),
}

impl Display for CompileProgError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            CompileProgError::AnalysisFailed(s) => s.fmt(f),
            CompileProgError::MissingMain => {
                write!(f, "{}", format_code!("missing function {}", "main"))
            }
            CompileProgError::CodeGenFailed(s) => write!(f, "{s}"),
        }
    }
}

/// Compiles a module.
#[flame]
fn build(target_mod: &str, quiet: bool, config: CodeGenConfig) -> Result<(), CompileProgError> {
    // Read and analyze the program.
    let start_time = Instant::now();
    let is_exe = config.output_format == OutputFormat::Executable;
    let output_path = config.output_path.to_str().unwrap().to_string();
    let (src_info, prog_analysis) = match analyze(target_mod, None, config) {
        Ok(p) => p,
        Err(e) => return Err(CompileProgError::AnalysisFailed(e)),
    };

    // Raise an error if there is no `fn main`.
    if prog_analysis.maybe_main_fn_tk.is_none() && is_exe {
        return Err(CompileProgError::MissingMain);
    }

    let prog = mono_prog(&src_info, prog_analysis);

    // Compile the program.
    if let Err(e) = gen_program(&src_info, prog) {
        return Err(CompileProgError::CodeGenFailed(e));
    }

    // Print the success message with the compile time.
    if !quiet {
        let total_duration = Instant::now() - start_time;
        println!(
            "Built {} ({}) in {}",
            target_mod,
            output_path,
            format_duration(total_duration)
        );
    }

    Ok(())
}

/// Compiles and runs Blang source code at the given path.
fn run(src_path: &str, config: CodeGenConfig) {
    let output_path = config.output_path.to_str().unwrap().to_string();

    if let Err(err) = build(src_path, true, config) {
        fatalln!("{}", err);
    }

    // Run the program.
    let io_err = process::Command::new(PathBuf::from(".").join(output_path)).exec();
    fatalln!("{}", io_err);
}

/// Generates a new default output file path of the form `bin/<src>.<output_format>`.
fn default_output_path(src: &Path, output_format: OutputFormat) -> PathBuf {
    let file_stem = src.file_stem().unwrap_or_default();
    let mut path = PathBuf::from("bin");
    path.push(PathBuf::from(file_stem).with_extension(output_format.file_extension()));
    path
}

#[cfg(test)]
mod tests {
    use crate::codegen::program::{CodeGenConfig, OutputFormat};
    use crate::{analyze, build, AnalyzeProgError};
    use std::collections::VecDeque;
    use std::fs;
    use std::path::PathBuf;
    use std::process::Child;

    #[test]
    fn build_std_lib() {
        // Run static analysis on all standard library code.
        let mut entries = fs::read_dir("std")
            .expect("should succeed")
            .collect::<VecDeque<_>>();

        while let Some(entry) = entries.pop_front() {
            let entry = entry.unwrap();
            let lib_path = entry.path();
            if lib_path.starts_with("std/builtins") {
                continue;
            }

            if lib_path.is_dir() {
                let mut has_src_files = false;
                for child in fs::read_dir(&lib_path).expect("should succeed") {
                    let child_ref = child.as_ref().unwrap();
                    if child_ref.file_type().unwrap().is_file()
                        && child_ref.path().extension().unwrap().to_str().unwrap() == "bl"
                    {
                        has_src_files = true;
                    }

                    entries.push_back(child);
                }

                // Skip dirs with no source files.
                if !has_src_files {
                    continue;
                }
            }

            let output_path = format!("bin/{}.o", lib_path.file_stem().unwrap().to_str().unwrap());
            let result = analyze(
                lib_path.to_str().unwrap(),
                None,
                CodeGenConfig::new_test_default(PathBuf::from(output_path), OutputFormat::LLVMIR),
            );

            match result {
                Ok(_) | Err(AnalyzeProgError::ModNotFound(_)) => {}
                Err(other) => panic!("{}", other),
            }
        }
    }

    #[test]
    fn build_tests_and_examples() {
        let mut paths = vec![];

        let test_entries = fs::read_dir("src/tests").expect("should succeed");
        for entry in test_entries {
            let path = entry.unwrap().path();
            if path.is_dir() {
                paths.push(path);
            }
        }

        let example_entries = fs::read_dir("docs/examples").expect("should succeed");
        for entry in example_entries {
            let path = entry.unwrap().path();
            if path.is_dir() {
                paths.push(path);
            }
        }

        let mut all_passed = true;
        let mut clang_procs = vec![];

        // Compile all the programs to IR and then spawn Clang processes to verify them and
        // generate executables for them.
        for path in paths {
            let src_path_stem = path.file_stem().unwrap().to_str().unwrap();
            let ir_path = format!("bin/{}.ll", src_path_stem);
            let exe_path = format!("bin/{}", src_path_stem);

            // Compile the source code to IR.
            let codegen_config =
                CodeGenConfig::new_test_default(PathBuf::from(&ir_path), OutputFormat::LLVMIR);
            build(path.to_str().unwrap(), true, codegen_config).unwrap();

            // Verify IR and build executable with Clang.
            let clang_proc = clang_build_verify(&ir_path, &exe_path);
            clang_procs.push((clang_proc, exe_path));
        }

        // Wait for all the Clang processes and make sure they succeeded. Then run executables and
        // check that they also succeed.
        for (clang_proc, exe_path) in clang_procs {
            let clang_output = clang_proc.wait_with_output().unwrap();
            if !clang_output.status.success() {
                eprintln!("clang failed with {}", clang_output.status);
                eprintln!("{}", String::from_utf8(clang_output.stderr).unwrap());
                all_passed = false;
                continue;
            }

            // Run the executable and make sure it succeeds.
            let exe_output = std::process::Command::new(&exe_path).output().unwrap();
            if !exe_output.status.success() {
                eprintln!("{exe_path}: failed with {}", exe_output.status);
                eprintln!("{}", String::from_utf8(exe_output.stderr).unwrap());
                all_passed = false;
            }
        }

        assert!(all_passed);
    }

    fn clang_build_verify(ir_path: &str, exe_path: &str) -> Child {
        std::process::Command::new("clang-18")
            .args([
                ir_path,
                "-O2",
                "-fverify-intermediate-code",
                "-fsanitize=undefined,address",
                "-fstack-protector-all",
                "-fno-sanitize-recover=all",
                "-Wall",
                "-Wno-override-module",
                "-Wextra",
                "-Wpedantic",
                "-Werror",
                "-o",
                exe_path,
            ])
            .spawn()
            .unwrap()
    }
}
