use std::fs::File;
use std::io::{BufRead, BufReader, Result};
use std::path::{Path, PathBuf};
use std::process;

use clap::{arg, ArgAction, Command};
use colored::*;

use compiler::program::ProgCompiler;
use lexer::token::Token;
use parser::program::Program;

use crate::analyzer::func::RichFnSig;
use crate::analyzer::program::RichProg;
use crate::lexer::error::LexError;
use crate::parser::error::ParseError;
use crate::syscall::syscall::all_syscalls;

mod analyzer;
mod compiler;
#[macro_use]
mod fmt;
mod lexer;
mod parser;
mod syscall;
mod util;

fn main() {
    // Define the root command.
    let cmd = Command::new("blang")
        .version(env!("CARGO_PKG_VERSION"))
        .author("Bruno Bachmann")
        .about("A bad programming language.")
        .subcommand_required(true)
        .arg_required_else_help(true);

    // Add the "build" subcommand for compiling.
    let cmd = cmd.subcommand(
        Command::new("build")
            .about("Build Blang source code")
            .arg(arg!([SRC_PATH]).required(true))
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
            .arg(arg!([SRC_PATH]).required(true)),
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
                analyze(file_path);
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

/// Performs static analysis on the source code at the given path.
fn analyze(input_path: &str) -> Option<(RichProg, Vec<RichFnSig>)> {
    // Get a reader from the source file.
    let reader = match open_file(input_path) {
        Ok(r) => r,
        Err(err) => fatalln!(r#"error opening file "{}": {}"#, input_path, err),
    };

    // Break the file into tokens.
    let mut tokens = match Token::tokenize(reader.lines()) {
        Ok(tokens) => tokens,
        Err(LexError { message, line, col }) => {
            fatalln!(
                "{}\n  {}",
                message.bold(),
                format_file_loc(input_path, Some(line), Some(col)),
            )
        }
    };

    // Parse the program.
    let prog = match Program::from(&mut tokens) {
        Err(ParseError {
            kind: _,
            message,
            token: _,
            start_pos,
            ..
        }) => {
            fatalln!(
                "{}\n  {}",
                message.bold(),
                format_file_loc(input_path, Some(start_pos.line), Some(start_pos.col)),
            );
        }
        Ok(p) => p,
    };

    // Analyze the program.
    let analysis = RichProg::analyze(prog, all_syscalls().to_vec());
    if analysis.errors.is_empty() {
        return Some((analysis.prog, analysis.extern_fns));
    }

    // Print warnings.
    for warn in analysis.warnings {
        warnln!(
            "{}\n  {}\n",
            format!("{}", warn.message).bold(),
            format_file_loc(
                input_path,
                Some(warn.start_pos.line),
                Some(warn.start_pos.col)
            ),
        );
    }

    // Print errors.
    for err in analysis.errors {
        errorln!(
            "{}\n  {}",
            format!("{}: {}", err.kind, err.message).bold(),
            format_file_loc(
                input_path,
                Some(err.start_pos.line),
                Some(err.start_pos.col)
            ),
        );

        if let Some(detail) = err.detail {
            println!("  {}", detail);
        }

        if let Some(hint) = err.hint {
            println!("  {} {}", "hint:".green(), hint);
        }

        println!();
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
    let (prog, extern_fns) = match analyze(src_path) {
        Some(v) => v,
        None => return,
    };

    // If no output path was specified, just use the source file name.
    let src = Path::new(src_path);
    let dst = if let Some(path) = dst_path {
        PathBuf::from(path)
    } else {
        let file_stem = src.file_stem().unwrap_or_default();
        src.with_file_name(file_stem).with_extension(".ll")
    };

    // Compile the program.
    if let Err(e) = ProgCompiler::compile(
        &prog,
        extern_fns,
        target,
        as_bitcode,
        dst.as_path(),
        simplify_ir,
    ) {
        fatalln!("{}", e);
    }
}

/// Formats the file location has a colored string.
fn format_file_loc(path: &str, line: Option<usize>, col: Option<usize>) -> ColoredString {
    match (line, col) {
        (Some(l), Some(c)) => format!("--> {}:{}:{}", path, l, c).bright_black().bold(),
        _ => format!("--> {}", path).bright_black(),
    }
}
