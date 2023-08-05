use std::collections::VecDeque;
use std::fs::File;
use std::io::{stdin, stdout, BufRead, BufReader, Error, ErrorKind, Result, Write};
use std::process;

use clap::{arg, Command};
use colored::*;

use compiler::program::ProgCompiler;
use lexer::token::Token;
use parser::program::Program;
use parser::statement::Statement;

use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::program::RichProg;
use crate::analyzer::statement::RichStatement;
use crate::syscall::syscall::all_syscalls;

mod analyzer;
mod compiler;
mod lexer;
mod parser;
mod syscall;
mod util;

macro_rules! fatal {
    ($($arg:tt)*) => {{
        error!($($arg)*);
        process::exit(1);
    }};
}

macro_rules! error {
    ($($arg:tt)*) => {{
        print!("{}", "error: ".red().bold());
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
            .about("Builds a binary from Blang source code")
            .arg(arg!([SRC_PATH]).required(true))
            .arg(
                arg!(-u --unoptimized ... "Prevents simplification of generated LLVM IR")
                    .required(false),
            )
            .arg(arg!(-t --target <TARGET> "Specifies target ISA triple").required(false))
            .arg(arg!(-b --bitcode <BC_PATH> "Specifies bitcode output file path").required(false))
            .arg(arg!(-i --ir <LL_PATH> "Specifies LLVM IR output file path").required(false)),
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
            Some(file_path) => {
                let target = sub_matches.get_one::<String>("target");
                let bc_path = sub_matches.get_one::<String>("bitcode");
                let ir_path = sub_matches.get_one::<String>("ir");
                let simplify_ir = *sub_matches.get_one::<u8>("unoptimized").unwrap() == 0;
                compile(file_path, bc_path, ir_path, target, simplify_ir);
            }
            _ => fatal!("expected source path"),
        },
        Some(("repl", _)) => repl(),
        Some(("check", sub_matches)) => match sub_matches.get_one::<String>("SRC_PATH") {
            Some(file_path) => {
                analyze(file_path);
            }
            _ => fatal!("expected source path"),
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
fn analyze(input_path: &str) -> RichProg {
    // Get a reader from the source file.
    let reader = match open_file(input_path) {
        Ok(r) => r,
        Err(err) => fatal!(r#"error opening file "{}": {}"#, input_path, err),
    };

    // Break the file into tokens.
    let mut tokens = match Token::tokenize(reader.lines()) {
        Ok(tokens) => tokens,
        Err(e) => fatal!("{}", e),
    };

    // Parse the program.
    let prog = match Program::from(&mut tokens) {
        Err(e) => fatal!("{}", e),
        Ok(p) => p,
    };

    // Analyze the program.
    match RichProg::from(prog, all_syscalls().to_vec()) {
        Ok(rp) => rp,
        Err(e) => fatal!("{}", e),
    }
}

/// Compiles a source file for the given target ISA. If there is no target, infers configuration
/// for the current system.
fn compile(
    input_path: &str,
    bc_path: Option<&String>,
    ll_path: Option<&String>,
    target: Option<&String>,
    simplify_ir: bool,
) {
    // Read and analyze the program.
    let prog = analyze(input_path);

    // Compile the program.
    if let Err(e) = ProgCompiler::compile(&prog, target, bc_path, ll_path, simplify_ir) {
        fatal!("{}", e);
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
                                error!("{}", e);
                                break;
                            }
                        },
                        Err(e) => {
                            error!("{}", e);
                            break;
                        }
                    };

                    dbg!(&statement);
                    // TODO: generate IR
                }
            }
            Err(e) => error!("{}", e),
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
