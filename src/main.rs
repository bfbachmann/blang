use std::collections::{HashSet, VecDeque};
use std::fs::File;
use std::io::prelude::*;
use std::os::unix::prelude::CommandExt;
use std::path::{Path, PathBuf};
use std::time::Instant;
use std::{fs, process};

use clap::{arg, Arg, ArgAction, Command};
use flamer::flame;
use inkwell::targets::{RelocMode, TargetMachine};
use inkwell::OptimizationLevel;

use parser::module::Module;

use crate::analyzer::analyze::{analyze_modules, ProgramAnalysis};
use crate::codegen::program::{generate, init_target, CodeGenConfig, OutputFormat};
use crate::fmt::{display_err, format_duration};
use crate::lexer::error::LexResult;
use crate::lexer::lex::lex;
use crate::lexer::pos::Locatable;
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::mono_collector::mono_prog;

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
            .arg(arg!([SRC_PATH] "Path to the source code to compile").required(true))
            .arg(
                arg!(-O --"optimization-level" <OPT_LEVEL> "Optimization level")
                    .required(false)
                    .value_parser(["default", "none", "less", "aggressive"]),
            )
            .arg(
                arg!(--"reloc-mode" <RELOC_MODE> "Relocation mode")
                    .required(false)
                    .value_parser(["default", "pic", "dynamic-no-pic", "static"]),
            )
            .arg(
                arg!(-q --quiet ... "Don't print log messages")
                    .required(false)
                    .action(ArgAction::SetTrue),
            )
            .arg(arg!(-t --target <TARGET> "Target ISA triple").required(false))
            .arg(
                arg!(-f --format <FORMAT> "Output file format")
                    .required(false)
                    .value_parser(["exe", "ir", "bc", "obj", "asm"]),
            )
            .arg(arg!(-o --out <OUTPUT_PATH> "Output file path").required(false))
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

    // Add the "check" subcommand for performing static analysis.
    let cmd = cmd.subcommand(
        Command::new("check")
            .about("Perform static analysis only")
            .arg(arg!([SRC_PATH] "Path to the source code to check").required(true))
            .arg(arg!(-d --dump <DUMP_PATH> "Dump the analyzed AST to a file").required(false)),
    );

    // Add the "run" subcommand for building and running a binary.
    let cmd = cmd.subcommand(
        Command::new("run")
            .about("Run Blang source code")
            .arg(arg!([SRC_PATH] "Path to the source code to run").required(true)),
    );

    let matches = cmd.get_matches();

    // Handle the command.
    match matches.subcommand() {
        Some(("build", sub_matches)) => match sub_matches.get_one::<String>("SRC_PATH") {
            Some(src_path) => {
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
                        "static" => RelocMode::Static,
                        _ => unreachable!(),
                    },

                    None => RelocMode::Default,
                };

                let target_machine = match init_target(
                    sub_matches.get_one::<String>("target"),
                    optimization_level,
                    reloc_mode,
                ) {
                    Ok(machine) => machine,
                    Err(err) => fatalln!("{err}"),
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
                        let src = Path::new(src_path);
                        default_output_file_path(src, output_format)
                    }
                };

                let quiet = sub_matches.get_flag("quiet");

                let linker = sub_matches.get_one::<String>("linker");

                let linker_args = sub_matches
                    .get_many::<String>("linker-flag")
                    .unwrap_or_default()
                    .collect();

                let codegen_config = CodeGenConfig {
                    output_path: &output_path,
                    output_format,
                    target_machine: &target_machine,
                    optimization_level,
                    linker,
                    linker_args,
                };

                if let Err(e) = compile(src_path, quiet, codegen_config) {
                    fatalln!("{}", e);
                }
            }
            _ => fatalln!("expected source path"),
        },

        Some(("check", sub_matches)) => match sub_matches.get_one::<String>("SRC_PATH") {
            Some(file_path) => {
                let maybe_dump_path = sub_matches.get_one::<String>("dump");
                if let Err(e) = analyze(file_path, maybe_dump_path) {
                    fatalln!("{}", e);
                };
            }
            _ => fatalln!("expected source path"),
        },

        Some(("run", sub_matches)) => match sub_matches.get_one::<String>("SRC_PATH") {
            Some(file_path) => {
                let target_machine =
                    match init_target(None, OptimizationLevel::Default, RelocMode::Default) {
                        Ok(machine) => machine,
                        Err(err) => fatalln!("{err}"),
                    };
                run(file_path, &target_machine);
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

/// Parses source code. If `input_path` is a directory, we'll try to locate and parse
/// the `main.bl` file inside it along with any imported paths. Otherwise, the file
/// at `input_path` and all its imports will be parsed.
/// Prints parse errors and exits if there were any parse errors. Otherwise,
/// returns parse sources.
// TODO: Allow compilation of bare modules (without `main`).
#[flame]
fn parse_source_files(input_path: &str) -> Result<Vec<Module>, String> {
    let is_dir = match fs::metadata(input_path) {
        Ok(meta) => meta.is_dir(),
        Err(err) => return Err(format!(r#"error reading "{}": {}"#, input_path, err)),
    };

    // Get the project root directory and main file paths.
    let mut file_paths = if is_dir {
        let root_path = fs::canonicalize(input_path).unwrap();
        let main_path = root_path.join("main.bl");

        if !main_path.exists() {
            let mut paths = vec![];
            match fs::read_dir(root_path.to_str().unwrap()) {
                Ok(entries) => {
                    // Collect all source files in the directory.
                    for result in entries {
                        match result {
                            Ok(entry) => {
                                let is_bl = entry.file_name().to_str().unwrap().ends_with(".bl");
                                let is_file = entry.file_type().is_ok_and(|ft| ft.is_file());
                                if is_file && is_bl {
                                    paths.push(entry.path());
                                }
                            }
                            _ => continue,
                        };
                    }
                }

                Err(err) => return Err(format!(r#"error reading "{}": {}"#, input_path, err)),
            };

            paths
        } else {
            let main_path = Path::new(input_path);
            vec![main_path.join("main.bl")]
        }
    } else {
        let main_path = Path::new(input_path);
        vec![main_path.to_path_buf()]
    };

    // Include builtins.
    match fs::read_dir("std/builtins") {
        Ok(entries) => {
            for entry in entries {
                match entry {
                    Ok(entry) => {
                        file_paths.push(entry.path());
                    }

                    Err(err) => return Err(err.to_string()),
                }
            }
        }

        Err(err) => return Err(err.to_string()),
    };

    // Parse all source files by following imports.
    let mut files_to_parse = VecDeque::from(file_paths);
    let mut parsed_mod_paths: HashSet<PathBuf> = HashSet::new();
    let mut parsed_mods = vec![];
    let mut parse_error_count = 0;
    while let Some(path) = files_to_parse.pop_front() {
        let path = path.to_str().unwrap();

        // Lex the source file and return early if there are any errors.
        let tokens = match lex_source_file(path)? {
            Ok(tokens) => tokens,
            Err(err) => {
                display_err(
                    err.message.as_str(),
                    None,
                    None,
                    input_path,
                    &err.span,
                    false,
                );

                return Err("analysis skipped due to previous error".to_string());
            }
        };

        // Parse the source file and log any parse errors.
        match Module::from(path, &mut Stream::from(tokens)) {
            Ok(module) => {
                for used_mod in &module.used_mods {
                    let used_mod_path = PathBuf::from(used_mod.path.raw.as_str());

                    // Make sure the path is actually a file we can access.
                    if !used_mod_path.exists() {
                        parse_error_count += 1;
                        display_err(
                            format_code!("{} does not exist", used_mod_path.display()).as_str(),
                            None,
                            None,
                            path,
                            used_mod.path.span(),
                            false,
                        );

                        continue;
                    }

                    if used_mod_path.is_dir() {
                        parse_error_count += 1;
                        display_err(
                            format_code!("{} is not a file", used_mod_path.display()).as_str(),
                            None,
                            None,
                            path,
                            used_mod.path.span(),
                            false,
                        );

                        continue;
                    }

                    if !parsed_mod_paths.contains(&used_mod_path) {
                        files_to_parse.push_back(used_mod_path)
                    }
                }

                parsed_mod_paths.insert(Path::new(module.path.as_str()).to_path_buf());
                parsed_mods.push(module);
            }

            Err(err) => {
                parse_error_count += 1;
                display_err(err.message.as_str(), None, None, path, err.span(), false)
            }
        };
    }

    // Abort if there are parse errors.
    if parse_error_count > 0 {
        return Err(format!(
            "analysis skipped due to previous {}",
            match parse_error_count {
                1 => "error".to_string(),
                n => format!("{} errors", n),
            }
        ));
    }

    Ok(parsed_mods)
}

/// Lexes a source file.
fn lex_source_file(input_path: &str) -> Result<LexResult<Vec<Token>>, String> {
    let full_path = match fs::canonicalize(input_path) {
        Ok(p) => p,
        Err(err) => return Err(format!("error reading {}: {}", input_path, err)),
    };

    let source_code = match fs::read_to_string(full_path) {
        Ok(code) => code,
        Err(err) => return Err(format!("error reading {}: {}", input_path, err)),
    };

    Ok(lex(source_code.as_str()))
}

/// Performs static analysis on the source code at the given path. If `input_path` is a directory,
/// all source files therein will be analyzed. Returns the analyzed set of sources, or logs an
/// error and exits with code 1.
#[flame]
fn analyze(input_path: &str, maybe_dump_path: Option<&String>) -> Result<ProgramAnalysis, String> {
    // Parse all targeted source files.
    let modules = parse_source_files(input_path)?;
    if modules.is_empty() {
        return Err(format!("no source files found in {}", input_path));
    }

    // Analyze the program.
    let analysis = analyze_modules(modules);

    // Display warnings and errors that occurred.
    let mut err_count = 0;
    for result in &analysis.analyzed_modules {
        let path = result.module.path.clone();

        // Print warnings.
        for warn in &result.warnings {
            display_err(
                warn.message.as_str(),
                None,
                None,
                path.as_str(),
                &warn.span,
                true,
            );
        }

        // Print errors.
        for err in &result.errors {
            let path = result.module.path.clone();
            err_count += 1;

            display_err(
                err.message.as_str(),
                err.detail.as_ref(),
                err.help.as_ref(),
                path.as_str(),
                &err.span,
                false,
            );
        }
    }

    // Die if analysis failed.
    if err_count > 0 {
        return Err(format!(
            "analysis failed with {}",
            match err_count {
                1 => "error".to_string(),
                n => format!("{} errors", n),
            }
        ));
    }

    // Dump the AST to a file, if necessary.
    if let Some(dump_path) = maybe_dump_path {
        let dst = Path::new(dump_path.as_str());
        let mut dst_file = match File::create(dst) {
            Err(err) => {
                return Err(format!(
                    "error opening file {}: {}",
                    dst.to_str().unwrap_or_default(),
                    err
                ));
            }
            Ok(result) => result,
        };

        if let Err(err) = write!(dst_file, "{:#?}", analysis.analyzed_modules) {
            return Err(format!(
                "error writing AST to file {}: {}",
                dst.to_str().unwrap_or_default(),
                err
            ));
        }
    }

    Ok(analysis)
}

/// Compiles a source files for the given target ISA. If `src_path` points to a directory, all
/// source files therein will be compiled. If there is no target, infers configuration
/// for the current host system.
#[flame]
fn compile(src_path: &str, quiet: bool, config: CodeGenConfig) -> Result<(), String> {
    // Read and analyze the program.
    let start_time = Instant::now();
    let prog_analysis = analyze(src_path, None)?;
    let prog = mono_prog(prog_analysis);

    // Compile the program.
    if let Err(e) = generate(prog, config) {
        return Err(format!("{}", e));
    }

    // Print the success message with the compile time.
    if !quiet {
        let total_duration = Instant::now() - start_time;
        println!(
            "Compiled {} in {}.\n",
            src_path,
            format_duration(total_duration)
        );
    }

    Ok(())
}

/// Compiles and runs Blang source code at the given path.
fn run(src_path: &str, target_machine: &TargetMachine) {
    // Read and analyze the program.
    let prog_analysis = match analyze(src_path, None) {
        Ok(pa) => pa,
        Err(e) => fatalln!("{}", e),
    };

    // Find all relevant functions that we need to generate code for.
    let prog = mono_prog(prog_analysis);

    // Set output executable path to the source path without the extension.
    let src = Path::new(src_path);
    let dst = default_output_file_path(src, OutputFormat::Executable);

    // Compile the program.
    if let Err(e) = generate(
        prog,
        CodeGenConfig::new_default(target_machine, dst.as_path(), OutputFormat::Executable),
    ) {
        fatalln!("{}", e);
    }

    // Run the program.
    let io_err = process::Command::new(PathBuf::from(".").join(dst)).exec();
    fatalln!("{}", io_err);
}

/// Generates a new default output file path of the form `bin/<src>.<output_format>`.
fn default_output_file_path(src: &Path, output_format: OutputFormat) -> PathBuf {
    let file_stem = src.file_stem().unwrap_or_default();
    let mut path = PathBuf::from("bin");
    path.push(
        PathBuf::from(file_stem).with_extension(match output_format {
            OutputFormat::LLVMBitcode => "bc",
            OutputFormat::LLVMIR => "ll",
            OutputFormat::Assembly => "s",
            OutputFormat::Object => "o",
            OutputFormat::Executable => "",
        }),
    );
    path
}

#[cfg(test)]
mod tests {
    use crate::codegen::program::{init_default_host_target, CodeGenConfig, OutputFormat};
    use crate::compile;
    use std::fs;
    use std::path::Path;
    use std::process::Child;

    #[test]
    fn build_std_lib() {
        // Check that we can compile the standard library.
        let target = init_default_host_target().unwrap();
        let entries = fs::read_dir("std").expect("should succeed");
        for entry in entries {
            let lib_path = entry.unwrap().path();
            if lib_path.starts_with("std/builtins") {
                continue;
            }

            let output_path = format!("bin/{}.o", lib_path.file_stem().unwrap().to_str().unwrap());

            // Compile the library.
            compile(
                lib_path.to_str().unwrap(),
                true,
                CodeGenConfig::new_default(&target, Path::new(&output_path), OutputFormat::Object),
            )
            .expect("should succeed");
        }
    }

    #[test]
    fn build_tests_and_examples() {
        let mut paths = vec![];

        let test_entries = fs::read_dir("src/tests").expect("should succeed");
        for entry in test_entries {
            let file_path = entry.unwrap().path();
            let path_str = file_path.to_str().unwrap();
            if !path_str.ends_with("_test.bl") {
                continue;
            }

            paths.push(file_path);
        }

        let example_entries = fs::read_dir("docs/examples").expect("should succeed");
        for entry in example_entries {
            let entry = entry.unwrap();
            if entry.metadata().unwrap().is_dir() {
                paths.push(entry.path());
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
            let target_machine = init_default_host_target().unwrap();
            let codegen_config = CodeGenConfig::new_default(
                &target_machine,
                Path::new(&ir_path),
                OutputFormat::LLVMIR,
            );
            compile(path.to_str().unwrap(), true, codegen_config).unwrap();

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
                &ir_path,
                "-O2",
                "-fsanitize=undefined,address",
                "-fstack-protector-all",
                "-fno-sanitize-recover=all",
                "-Wall",
                "-Wno-override-module",
                "-Wextra",
                "-Wpedantic",
                "-Werror",
                "-o",
                &exe_path,
            ])
            .spawn()
            .unwrap()
    }
}
