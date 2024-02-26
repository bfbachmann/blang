use std::collections::{HashSet, VecDeque};
use std::fs::File;
use std::io::prelude::*;
use std::io::{BufReader, Result};
use std::path::{Path, PathBuf};
use std::time::Instant;
use std::{fs, process};

use clap::{arg, ArgAction, Command};
use colored::*;

use parser::module::Module;

use crate::analyzer::analyze::{analyze_modules, ProgramAnalysis};
use crate::codegen::program::{generate, OutputFormat};
use crate::fmt::{display_err, format_file_loc};
use crate::lexer::error::LexError;
use crate::lexer::lex::lex;
use crate::lexer::pos::Locatable;
use crate::lexer::stream::Stream;
use crate::parser::ast::statement::Statement;
use crate::parser::error::ParseResult;

mod codegen;
#[macro_use]
mod fmt;
mod analyzer;
mod lexer;
mod parser;
mod util;

fn main() {
    // Define the root command.
    let cmd = Command::new("blang")
        .version(env!("CARGO_PKG_VERSION"))
        .author("Bruno Bachmann")
        .about("The Blang programming language.")
        .subcommand_required(true)
        .arg_required_else_help(true);

    // Add the "build" subcommand for compiling.
    let cmd = cmd.subcommand(
        Command::new("build")
            .about("Compile Blang source code to LLVM IR")
            .arg(arg!([SRC_PATH] "Path to the source code to compile").required(true))
            .arg(
                arg!(-u --unoptimized ... "Prevent simplification of generated LLVM IR")
                    .required(false)
                    .action(ArgAction::SetTrue),
            )
            .arg(
                arg!(-q --quiet ... "Don't print log messages")
                    .required(false)
                    .action(ArgAction::SetTrue),
            )
            .arg(arg!(-t --target <TARGET> "Target ISA triple").required(false))
            .arg(
                arg!(-f --format <FORMAT> "The output format to generate")
                    .required(false)
                    .default_value("exe")
                    .value_parser(["exe", "ir", "bc", "obj", "asm"]),
            )
            .arg(arg!(-o --out <OUTPUT_PATH> "Output file path").required(false))
            .arg(arg!(-l --linker <LINKER> "Linker to use").required(false))
            .arg(
                arg!(-L --"linker-flags" <LINKER_FLAGS> "Linker flags")
                    .required(false)
                    .num_args(1..)
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

    // Handle the command.
    match cmd.get_matches().subcommand() {
        Some(("build", sub_matches)) => match sub_matches.get_one::<String>("SRC_PATH") {
            Some(src_path) => {
                let target = sub_matches.get_one::<String>("target");
                let output_format = match sub_matches.get_one::<String>("format").unwrap().as_str()
                {
                    "obj" => OutputFormat::Object,
                    "ir" => OutputFormat::LLVMIR,
                    "bc" => OutputFormat::LLVMBitcode,
                    "asm" => OutputFormat::Assembly,
                    "exe" => OutputFormat::Executable,
                    _ => unreachable!(),
                };
                let dst_path = sub_matches.get_one::<String>("out");
                let optimize = !sub_matches.get_flag("unoptimized");
                let quiet = sub_matches.get_flag("quiet");
                let linker = sub_matches.get_one::<String>("linker");
                let linker_flags = sub_matches
                    .get_many::<String>("linker-flags")
                    .unwrap_or_default()
                    .collect();
                compile(
                    src_path,
                    dst_path,
                    output_format,
                    target,
                    optimize,
                    quiet,
                    linker,
                    linker_flags,
                );
            }
            _ => fatalln!("expected source path"),
        },
        Some(("check", sub_matches)) => match sub_matches.get_one::<String>("SRC_PATH") {
            Some(file_path) => {
                let maybe_dump_path = sub_matches.get_one::<String>("dump");
                analyze(file_path, maybe_dump_path);
            }
            _ => fatalln!("expected source path"),
        },
        _ => unreachable!("no subcommand"),
    };
}

/// Opens the file at the given path and returns a reader for it.
fn open_file(file_path: &str) -> Result<Stream<char>> {
    let file = File::open(file_path)?;
    let mut reader = BufReader::new(file);

    let mut contents = String::new();
    reader.read_to_string(&mut contents)?;

    Ok(Stream::from(contents.chars().collect()))
}

/// Parses source code. If `input_path` is a directory, we'll try to locate and parse
/// the `main.bl` file inside it along with any imported paths. Otherwise, the file
/// at `input_path` and all its imports will be parsed.
/// Prints parse errors and exits if there were any parse errors. Otherwise,
/// returns parse sources.
// TODO: Allow compilation of bare modules (without `main`).
fn parse_source_files(input_path: &str) -> Vec<Module> {
    let is_dir = match fs::metadata(input_path) {
        Ok(meta) => meta.is_dir(),
        Err(err) => fatalln!(r#"error reading "{}": {}"#, input_path, err),
    };

    // Get the project root directory and main file paths.
    let (root_path, main_paths) = if is_dir {
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

                Err(err) => {
                    fatalln!(r#"error reading "{}": {}"#, input_path, err)
                }
            };

            (root_path.to_path_buf(), paths)
        } else {
            (root_path.to_path_buf(), vec![main_path.to_path_buf()])
        }
    } else {
        let main_path = Path::new(input_path);
        (
            main_path.parent().unwrap().to_path_buf(),
            vec![main_path.to_path_buf()],
        )
    };

    // Parse all source files by following imports.
    let mut files_to_parse = VecDeque::from(main_paths);
    let mut parsed_mod_paths: HashSet<PathBuf> = HashSet::new();
    let mut parsed_mods = vec![];
    let mut parse_error_count = 0;
    while let Some(path) = files_to_parse.pop_front() {
        match parse_source_file(path.to_str().unwrap()) {
            Ok(module) => {
                for statement in &module.statements {
                    if let Statement::Use(used_mod) = statement {
                        let used_mod_path = PathBuf::from(used_mod.path.raw.as_str());
                        let full_used_mod_path = root_path.join(used_mod_path);
                        if !parsed_mod_paths.contains(&full_used_mod_path) {
                            files_to_parse.push_back(full_used_mod_path)
                        }
                    }
                }

                parsed_mod_paths.insert(Path::new(module.path.as_str()).to_path_buf());
                parsed_mods.push(module);
            }

            Err(err) => {
                parse_error_count += 1;
                display_err(
                    err.message.as_str(),
                    None,
                    None,
                    path.to_str().unwrap(),
                    err.start_pos(),
                    err.end_pos(),
                    false,
                )
            }
        };
    }

    // Abort early if there are parse errors.
    if parse_error_count > 0 {
        fatalln!(
            "analysis skipped due to previous {}",
            match parse_error_count {
                1 => "error".to_string(),
                n => format!("{} errors", n),
            }
        )
    }

    parsed_mods
}

/// Lexes and parses a source file.
fn parse_source_file(input_path: &str) -> ParseResult<Module> {
    // Get a stream of characters from the source file.
    let mut char_stream = match open_file(input_path) {
        Ok(r) => r,
        Err(err) => fatalln!(r#"error opening file "{}": {}"#, input_path, err),
    };

    // Break the char stream into tokens.
    let tokens = match lex(&mut char_stream) {
        Ok(tokens) => tokens,
        Err(LexError { message, line, col }) => {
            fatalln!(
                "{}\n  {}\n  This syntax error prevents any further program analysis.",
                message.bold(),
                format_file_loc(input_path, Some(line), Some(col)),
            );
        }
    };

    // Parse the program.
    Module::from(input_path, &mut Stream::from(tokens))
}

/// Performs static analysis on the source code at the given path. If `input_path` is a directory,
/// all source files therein will be analyzed. Returns the analyzed set of sources, or logs an
/// error and exits with code 1.
fn analyze(input_path: &str, maybe_dump_path: Option<&String>) -> ProgramAnalysis {
    // Parse all targeted source files.
    let modules = parse_source_files(input_path);

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
                &warn.start_pos,
                &warn.end_pos,
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
                &err.start_pos,
                &err.end_pos,
                false,
            );
        }
    }

    // Die if analysis failed.
    if err_count > 0 {
        fatalln!(
            "analysis failed due to previous {}",
            match err_count {
                1 => "error".to_string(),
                n => format!("{} errors", n),
            }
        )
    }

    // Dump the AST to a file, if necessary.
    if let Some(dump_path) = maybe_dump_path {
        let dst = Path::new(dump_path.as_str());
        let mut dst_file = match File::create(dst) {
            Err(err) => {
                fatalln!(
                    "error opening file {}: {}",
                    dst.to_str().unwrap_or_default(),
                    err
                );
            }
            Ok(result) => result,
        };

        if let Err(err) = write!(dst_file, "{:#?}", analysis) {
            fatalln!(
                "error writing AST to file {}: {}",
                dst.to_str().unwrap_or_default(),
                err
            );
        }
    }

    analysis
}

/// Compiles a source files for the given target ISA. If `src_path` points to a directory, all
/// source files therein will be compiled. If there is no target, infers configuration
/// for the current host system.
fn compile(
    src_path: &str,
    dst_path: Option<&String>,
    output_format: OutputFormat,
    target: Option<&String>,
    optimize: bool,
    quiet: bool,
    linker: Option<&String>,
    linker_flags: Vec<&String>,
) {
    let start_time = Instant::now();

    // Read and analyze the program.
    let prog_analysis = analyze(src_path, None);

    // If no output path was specified, just use the source file name.
    let src = Path::new(src_path);
    let dst = if let Some(path) = dst_path {
        PathBuf::from(path)
    } else {
        let file_stem = src.file_stem().unwrap_or_default();
        PathBuf::from(file_stem).with_extension(match output_format {
            OutputFormat::LLVMBitcode => "bc",
            OutputFormat::LLVMIR => "ll",
            OutputFormat::Assembly => "s",
            OutputFormat::Object => "o",
            OutputFormat::Executable => "",
        })
    };

    // Compile the program.
    if let Err(e) = generate(
        prog_analysis
            .analyzed_modules
            .into_iter()
            .map(|s| s.module)
            .collect(),
        prog_analysis.type_store,
        target,
        output_format,
        dst.as_path(),
        optimize,
        linker,
        linker_flags,
    ) {
        fatalln!("{}", e);
    }

    // Print the success message with the compile time.
    if !quiet {
        let compile_time = Instant::now() - start_time;
        println!(
            "Compiled {} in {}.{}s.",
            src_path,
            compile_time.as_secs(),
            compile_time.subsec_millis()
        )
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use crate::codegen::program::OutputFormat;
    use crate::compile;

    #[test]
    fn compile_all_test_files() {
        // Check that all the `_test.bl` files in src/tests compile.
        let entries = fs::read_dir("src/tests").expect("should succeed");
        for entry in entries {
            let file_path = entry.unwrap().path();
            if !file_path.to_str().unwrap().ends_with("_test.bl") {
                continue;
            }

            let output_path = format!("bin/{}.o", file_path.file_stem().unwrap().to_str().unwrap());

            compile(
                file_path.to_str().unwrap(),
                Some(&output_path),
                OutputFormat::Object,
                None,
                true,
                true,
                None,
                vec![],
            );
        }
    }

    #[test]
    fn compile_all_libs() {
        // Check that we can compile the standard library.
        let entries = fs::read_dir("lib").expect("should succeed");
        for entry in entries {
            let lib_path = entry.unwrap().path();
            let output_path = format!("bin/{}.o", lib_path.file_stem().unwrap().to_str().unwrap());

            compile(
                lib_path.to_str().unwrap(),
                Some(&output_path),
                OutputFormat::Object,
                None,
                true,
                true,
                None,
                vec![],
            );
        }
    }
}
