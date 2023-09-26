use std::fs::File;
use std::io::{BufRead, BufReader, Result};
use std::path::{Path, PathBuf};
use std::process;
use std::process::exit;

use clap::{arg, ArgAction, Command};
use colored::*;

use compiler::program::ProgCompiler;
use lexer::token::Token;
use parser::program::Program;

use crate::analyzer::program::{ProgramAnalysis, RichProg};
use crate::fmt::format_file_loc;
use crate::lexer::error::LexError;
use crate::parser::error::ParseError;
use crate::parser::stream::Stream;

mod analyzer;
mod compiler;
#[macro_use]
mod fmt;
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
            .arg(arg!(-t --target <TARGET> "Target ISA triple").required(false))
            .arg(
                arg!(-b --bitcode "Output LLVM bitcode")
                    .required(false)
                    .action(ArgAction::SetTrue),
            )
            .arg(arg!(-o --out <OUTPUT_PATH> "Output file path").required(false)),
    );

    // Add the "check" subcommand for performing static analysis.
    let cmd = cmd.subcommand(
        Command::new("check")
            .about("Perform static analysis only")
            .arg(arg!([SRC_PATH] "Path to the source code to check").required(true)),
    );

    // Handle the command.
    match cmd.get_matches().subcommand() {
        Some(("build", sub_matches)) => match sub_matches.get_one::<String>("SRC_PATH") {
            Some(src_path) => {
                let target = sub_matches.get_one::<String>("target");
                let as_bitcode = sub_matches.get_flag("bitcode");
                let dst_path = sub_matches.get_one::<String>("out");
                let simplify_ir = !sub_matches.get_flag("unoptimized");
                compile(src_path, dst_path, as_bitcode, target, simplify_ir);
            }
            _ => fatalln!("expected source path"),
        },
        Some(("check", sub_matches)) => match sub_matches.get_one::<String>("SRC_PATH") {
            Some(file_path) => {
                if analyze(file_path).is_none() {
                    exit(1);
                }
            }
            _ => fatalln!("expected source path"),
        },
        _ => unreachable!("no subcommand"),
    };
}

/// Opens the file at the given path and returns a reader for it.
fn open_file(file_path: &str) -> Result<BufReader<File>> {
    let file = File::open(file_path)?;
    Ok(BufReader::new(file))
}

/// Performs static analysis on the source code at the given path. Returns a successfully analyzed
/// program and extern functions, or `None`.
fn analyze(input_path: &str) -> Option<ProgramAnalysis> {
    // Get a reader from the source file.
    let reader = match open_file(input_path) {
        Ok(r) => r,
        Err(err) => fatalln!(r#"error opening file "{}": {}"#, input_path, err),
    };

    // Break the file into tokens.
    let tokens = match Token::tokenize(reader.lines()) {
        Ok(tokens) => tokens,
        Err(LexError { message, line, col }) => {
            fatalln!(
                "{}\n  {}\n  This error prevents any further program analysis.",
                message.bold(),
                format_file_loc(input_path, Some(line), Some(col)),
            )
        }
    };

    // Parse the program.
    let prog = match Program::from(&mut Stream::from(tokens)) {
        Err(ParseError {
            kind: _,
            message,
            token: _,
            start_pos,
            ..
        }) => {
            fatalln!(
                "{}\n  {}\n  This error prevents any further program analysis.",
                message.bold(),
                format_file_loc(input_path, Some(start_pos.line), Some(start_pos.col)),
            );
        }
        Ok(p) => p,
    };

    // Analyze the program.
    let prog_analysis = RichProg::analyze(prog);

    // Print warnings.
    for warn in &prog_analysis.warnings {
        warnln!(
            "{}\n  {}\n",
            format!("{}", warn).bold(),
            format_file_loc(
                input_path,
                Some(warn.start_pos.line),
                Some(warn.start_pos.col)
            ),
        );
    }

    // Print errors.
    for err in &prog_analysis.errors {
        errorln!(
            "{}\n  {}",
            format!("{}: {}", err.kind, err.message).bold(),
            format_file_loc(
                input_path,
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

    // Return the program only if there were no errors.
    if prog_analysis.errors.is_empty() {
        return Some(prog_analysis);
    }

    None
}

/// Compiles a source file for the given target ISA. If there is no target, infers configuration
/// for the current system.
fn compile(
    src_path: &str,
    dst_path: Option<&String>,
    as_bitcode: bool,
    target: Option<&String>,
    simplify_ir: bool,
) {
    // Read and analyze the program.
    let prog_analysis = match analyze(src_path) {
        Some(v) => v,
        None => exit(1),
    };

    // If no output path was specified, just use the source file name.
    let src = Path::new(src_path);
    let dst = if let Some(path) = dst_path {
        PathBuf::from(path)
    } else {
        let file_stem = src.file_stem().unwrap_or_default();
        src.with_file_name(file_stem).with_extension("ll")
    };

    // Compile the program.
    if let Err(e) = ProgCompiler::compile(
        prog_analysis,
        target,
        as_bitcode,
        dst.as_path(),
        simplify_ir,
    ) {
        fatalln!("{}", e);
    }
}
