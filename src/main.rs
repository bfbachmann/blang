use std::collections::HashSet;
use std::fs::File;
use std::io::prelude::*;
use std::io::{BufReader, Result};
use std::ops::Sub;
use std::path::{Path, PathBuf};
use std::time::Instant;
use std::{fs, process};

use clap::{arg, ArgAction, Command};
use colored::*;

use parser::source::Source;

use crate::analyzer::analyze::{analyze_sources, ProgramAnalysis};
use crate::codegen::program::{generate, OutputFormat};
use crate::fmt::{display_msg, format_file_loc};
use crate::lexer::error::LexError;
use crate::lexer::lex::lex;

use crate::lexer::stream::Stream;
use crate::parser::ast::statement::Statement;
use crate::parser::error::{ParseError, ParseResult};

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
                    .default_value("obj")
                    .value_parser(["ir", "bc", "obj", "asm"]),
            )
            .arg(arg!(-o --out <OUTPUT_PATH> "Output file path").required(false)),
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
                    _ => unreachable!(),
                };
                let dst_path = sub_matches.get_one::<String>("out");
                let optimize = !sub_matches.get_flag("unoptimized");
                let quiet = sub_matches.get_flag("quiet");
                compile(src_path, dst_path, output_format, target, optimize, quiet);
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
fn parse_source_files(input_path: &str) -> Vec<Source> {
    let is_dir = match fs::metadata(input_path) {
        Ok(meta) => meta.is_dir(),
        Err(err) => fatalln!(r#"error reading "{}": {}"#, input_path, err),
    };

    // Collect up paths to source files.
    let main_path: String = if is_dir {
        let main_path = Path::new(input_path).join("main.bl");
        match main_path.exists() {
            true => main_path.to_str().unwrap().to_string(),
            false => fatalln!(r#"missing "{}""#, main_path.display()),
        }
    } else {
        input_path.to_string()
    };

    // Parse main source file.
    let parse_result = parse_source_file(main_path.as_str());

    // Parse any source files that were included via imports.
    let parsed_files: HashSet<String> = HashSet::from([main_path.clone()]);
    let mut all_parse_results = vec![(input_path.to_string(), parse_result)];
    if let Ok(source) = &all_parse_results[0].1 {
        let imported_paths: Vec<String> = source
            .statements
            .iter()
            .flat_map(|stmt| match stmt {
                Statement::Use(use_block) => use_block
                    .used_modules
                    .iter()
                    .map(|used_mod| {
                        Path::new(source.path.as_str())
                            .parent()
                            .unwrap()
                            .join(used_mod.path.raw.as_str())
                            .to_str()
                            .unwrap()
                            .to_string()
                    })
                    .collect(),
                _ => vec![],
            })
            .collect();

        let unique_import_paths = HashSet::from_iter(imported_paths.into_iter()).sub(&parsed_files);
        for path in unique_import_paths {
            let parse_result = parse_source_file(path.as_str());
            all_parse_results.push((path, parse_result));
        }
    }

    // Display any parse errors that occurred.
    let mut parse_error_count = 0;
    let mut sources = vec![];
    for (path, result) in all_parse_results.into_iter() {
        match result {
            Ok(source) => sources.push(source),
            Err(ParseError {
                kind: _,
                message,
                token: _,
                start_pos,
                end_pos,
            }) => {
                parse_error_count += 1;
                display_msg(
                    message.as_str(),
                    None,
                    None,
                    path.as_str(),
                    &start_pos,
                    &end_pos,
                    false,
                );
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

    sources
}

/// Lexes and parses a source file.
fn parse_source_file(input_path: &str) -> ParseResult<Source> {
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
    Source::from(input_path, &mut Stream::from(tokens))
}

/// Performs static analysis on the source code at the given path. If `input_path` is a directory,
/// all source files therein will be analyzed. Returns the analyzed set of sources, or logs an
/// error and exits with code 1.
fn analyze(input_path: &str, maybe_dump_path: Option<&String>) -> ProgramAnalysis {
    // Parse all targeted source files.
    let sources = parse_source_files(input_path);

    // Analyze the program.
    let analysis = analyze_sources(sources);

    // Display warnings and errors that occurred.
    let mut err_count = 0;
    for result in &analysis.analyzed_sources {
        let path = result.source.path.clone();

        // Print warnings.
        for warn in &result.warnings {
            display_msg(
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
            let path = result.source.path.clone();
            err_count += 1;

            display_msg(
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
        src.with_file_name(file_stem).with_extension("ll")
    };

    // Compile the program.
    if let Err(e) = generate(
        prog_analysis
            .analyzed_sources
            .into_iter()
            .map(|s| s.source)
            .collect(),
        prog_analysis.type_store,
        target,
        output_format,
        dst.as_path(),
        optimize,
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
            if !file_path.ends_with("_test.bl") {
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
            );
        }
    }
}
