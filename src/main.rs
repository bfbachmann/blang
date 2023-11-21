use std::fs::File;
use std::io::prelude::*;
use std::io::{BufReader, Result};
use std::path::{Path, PathBuf};
use std::time::Instant;
use std::{fs, process};

use clap::{arg, ArgAction, Command};
use colored::*;

use parser::source::Source;

use crate::analyzer::analyze::{analyze_sources, ProgramAnalysis};
use crate::codegen::program::{generate, OutputFormat};
use crate::fmt::format_file_loc;
use crate::lexer::error::LexError;
use crate::lexer::lex::lex;
use crate::lexer::stream::Stream;
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

/// Parses source code. If `input_path` is a directory, all source files within that
/// directory will be parsed. Otherwise, only the file at `input_path` will be parsed. Prints
/// parse errors and exits if there were any parse errors. Otherwise, returns parse sources.
fn parse_source_files(input_path: &str) -> Vec<Source> {
    let is_dir = match fs::metadata(input_path) {
        Ok(meta) => meta.is_dir(),

        Err(err) => fatalln!(r#"error reading "{}": {}"#, input_path, err),
    };

    // Collect up paths to source files.
    let file_paths: Vec<String> = if is_dir {
        let read_dir = match fs::read_dir(input_path) {
            Ok(read_dir) => read_dir,
            Err(err) => fatalln!(r#"error reading directory "{}": {}"#, input_path, err),
        };

        read_dir
            .into_iter()
            .map(|entry_result| {
                let entry = match entry_result {
                    Ok(e) => e,
                    Err(err) => fatalln!(r#"error reading directory entry: "{}""#, err),
                };

                entry.path().to_str().unwrap().to_string()
            })
            .filter(|path| path.ends_with(".bl"))
            .collect()
    } else {
        vec![input_path.to_string()]
    };

    // Parse source files.
    let parse_results: Vec<ParseResult<Source>> = file_paths
        .iter()
        .map(|path| parse_source_file(path))
        .collect();

    // Display any parse errors that occurred.
    let mut parse_error_count = 0;
    let mut sources = vec![];
    for (i, result) in parse_results.into_iter().enumerate() {
        match result {
            Ok(source) => sources.push(source),
            Err(ParseError {
                kind: _,
                message,
                token: _,
                start_pos,
                ..
            }) => {
                parse_error_count += 1;
                errorln!(
                    "{}\n  {}\n",
                    message.bold(),
                    format_file_loc(
                        file_paths[i].as_str(),
                        Some(start_pos.line),
                        Some(start_pos.col)
                    ),
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
            warnln!(
                "{}\n  {}\n",
                format!("{}", warn).bold(),
                format_file_loc(
                    path.as_str(),
                    Some(warn.start_pos.line),
                    Some(warn.start_pos.col)
                ),
            );

            println!();
        }

        // Print errors.
        for err in &result.errors {
            let path = result.source.path.clone();
            err_count += 1;

            errorln!(
                "{}\n  {}",
                format!("{}", err).bold(),
                format_file_loc(
                    path.as_str(),
                    Some(err.start_pos.line),
                    Some(err.start_pos.col)
                ),
            );

            if let Some(detail) = &err.detail {
                println!("  {}", detail);
            }

            if let Some(help) = &err.help {
                println!("  {} {}", "help:".green(), help);
            }

            println!();
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
        let mut dst_file = match File::create(dst.clone()) {
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
        let entries = fs::read_dir("src/tests").expect("should succeed");
        for entry in entries {
            let file_path = entry.unwrap().path();
            match file_path.extension() {
                Some(ext) if ext == "bl" => {}
                _ => continue,
            };

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
