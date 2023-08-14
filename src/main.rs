use std::collections::VecDeque;

use std::fs::File;
use std::io::{stdin, stdout, BufRead, BufReader, Error, ErrorKind, Result, Write};
use std::path::{Path, PathBuf};
use std::process;

use clap::{arg, ArgAction, Command};
use colored::*;

use crate::analyzer::func::RichFnSig;
use compiler::program::ProgCompiler;
use lexer::token::Token;
use parser::program::Program;
use parser::statement::Statement;

use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::program::RichProg;
use crate::analyzer::statement::RichStatement;
use crate::lexer::error::LexError;
use crate::parser::error::ParseError;
use crate::syscall::syscall::all_syscalls;

mod analyzer;
mod compiler;
mod lexer;
mod parser;
mod syscall;
mod util;

/// Prints an error message and exits with code 1.
macro_rules! fatalln {
    ($($arg:tt)*) => {{
        errorln!($($arg)*);
        process::exit(1);
    }};
}

/// Prints an error message.
macro_rules! errorln {
    ($($arg:tt)*) => {{
        print!("{}", "error: ".red().bold());
        println!($($arg)*);
    }};
}

/// Prints a warning message.
macro_rules! warnln {
    ($($arg:tt)*) => {{
        print!("{}", "warning: ".yellow().bold());
        println!($($arg)*);
    }};
}

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
            .about("Builds Blang source code")
            .arg(arg!([SRC_PATH]).required(true))
            .arg(
                arg!(-u --unoptimized ... "Prevents simplification of generated LLVM IR")
                    .required(false)
                    .action(ArgAction::SetTrue),
            )
            .arg(arg!(-t --target <TARGET> "Specifies target ISA triple").required(false))
            .arg(
                arg!(-b --bitcode "Output LLVM bitcode")
                    .required(false)
                    .action(ArgAction::SetTrue),
            )
            .arg(arg!(-o --out <OUTPUT_PATH> "Output file path").required(false)),
    );

    // Add the "repl" subcommand for running a REPL.
    let cmd = cmd.subcommand(Command::new("repl").about("Runs a REPL"));

    // Add the "check" subcommand for performing static analysis.
    let cmd = cmd.subcommand(
        Command::new("check")
            .about("Performs static analysis")
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
        Some(("repl", _)) => repl(),
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

/// Starts a REPL. The REPL will prompt for input and try to interpret it as a statement, then
/// print the result of the statement.
fn repl() {
    println!("Starting REPL.");
    println!("Use ^C to exit. Enter two successive newlines to commit statements.");

    let mut ctx = ProgramContext::new();

    loop {
        match repl_collect_tokens() {
            Ok(tokens) => {
                let mut tokens = tokens;
                while !tokens.is_empty() {
                    let statement = match Statement::from(&mut tokens) {
                        Ok(statement) => match RichStatement::from(&mut ctx, statement) {
                            Ok(s) => s,
                            Err(e) => {
                                errorln!("{}", e);
                                break;
                            }
                        },
                        Err(e) => {
                            errorln!("{}", e);
                            break;
                        }
                    };

                    dbg!(&statement);
                    // TODO: generate IR
                }
            }
            Err(e) => errorln!("{}", e),
        };
    }
}

/// Collects tokens from stdin until the user is done with input (i.e. until they've hit enter twice
/// in a row).
fn repl_collect_tokens() -> Result<VecDeque<Token>> {
    let mut tokens = VecDeque::new();
    let mut line_num = 1;
    let mut out = stdout();

    out.write("----------------\n".as_bytes())?;

    loop {
        // Print a prompt based on whether this is the beginning of a new sequence or a continuation
        // of the last one.
        out.write_all(format!("{}", format!("{} > ", line_num).bold()).as_bytes())?;
        out.flush()?;
        line_num += 1;

        // Read input.
        let mut buf = String::new();
        stdin().read_line(&mut buf)?;

        // If the input is only whitespace, it means we're done collecting tokens and we should
        // parse what we've collected so far.
        let input = buf.as_str();
        if input.trim().is_empty() {
            break;
        }

        // Tokenize input.
        match Token::tokenize_line(input, line_num) {
            Ok(new_tokens) => tokens.extend(new_tokens),
            Err(e) => return Err(Error::new(ErrorKind::InvalidInput, e)),
        };
    }

    Ok(tokens)
}

/// Formats the file location has a colored string.
fn format_file_loc(path: &str, line: Option<usize>, col: Option<usize>) -> ColoredString {
    match (line, col) {
        (Some(l), Some(c)) => format!("--> {}:{}:{}", path, l, c).bright_black().bold(),
        _ => format!("--> {}", path).bright_black(),
    }
}
