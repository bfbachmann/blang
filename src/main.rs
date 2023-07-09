extern crate core;

use std::collections::VecDeque;
use std::fs::File;
use std::io::{stdin, stdout, BufRead, BufReader, Error, ErrorKind, Result, Write};
use std::process;

use clap::{arg, Command};
use log::{error, info, set_max_level, Level};

use lexer::token::Token;
use parser::program::Program;
use parser::statement::Statement;

use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::program::analyze_program;
use crate::analyzer::statement::analyze_statement;
use crate::codegen::IRGenerator;

mod analyzer;
mod codegen;
mod lexer;
mod parser;
mod util;

macro_rules! fatal {
    ($($arg:tt)*) => {{
        error!($($arg)*);
        process::exit(1);
    }};
}

fn main() {
    // Set log level.
    env_logger::init();
    set_max_level(Level::Debug.to_level_filter());

    // Define commands.
    let matches = Command::new("blang")
        .version("0.1")
        .author("Bruno Bachmann")
        .about("A bad programming language.")
        .subcommand_required(true)
        .arg_required_else_help(true)
        .subcommand(
            Command::new("build")
                .about("Builds a binary from Blang source code")
                .arg(arg!([SRC_PATH]).required(true))
                .arg(arg!(-t --target <TARGET> "Specifies target ISA triple").required(false)),
        )
        .subcommand(Command::new("repl").about("Runs a REPL"))
        .get_matches();

    // Get file name from command line argument. If there is none, start a repl.
    match matches.subcommand() {
        Some(("build", sub_matches)) => match sub_matches.get_one::<String>("SRC_PATH") {
            Some(file_path) => {
                let target = sub_matches.get_one::<String>("target");
                compile(file_path, target)
            }
            _ => fatal!("Expected source path"),
        },
        Some(("repl", _)) => repl(),
        _ => unreachable!("No subcommand"),
    };
}

/// Opens the file at the given path and returns a reader for it.
fn open_file(file_path: &str) -> Result<BufReader<File>> {
    let file = File::open(file_path)?;
    Ok(BufReader::new(file))
}

/// Compiles a source file for the given target ISA. If there is no target, infers configuration
/// for the current system.
fn compile(input_path: &str, target: Option<&String>) {
    // Get a reader from the source file.
    let reader = match open_file(input_path) {
        Ok(r) => r,
        Err(err) => fatal!(r#"Error opening file "{}": {}"#, input_path, err),
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
    if let Err(e) = analyze_program(&prog) {
        fatal!("{}", e);
    }

    // Create IR generator.
    let ir_gen_result = match target {
        Some(t) => IRGenerator::new_for_target(t),
        None => IRGenerator::new(),
    };
    let mut ir_gen = match ir_gen_result {
        Ok(g) => g,
        Err(e) => fatal!("{}", e),
    };

    // Generate IR.
    match ir_gen.gen_prog(prog) {
        Ok(_) => {}
        Err(e) => fatal!("{}", e),
    };
}

/// Starts a REPL. The REPL will prompt for input and try to interpret it as a statement, then
/// print the result of the statement.
fn repl() {
    info!("Starting REPL.");
    info!("Use ^C to exit. Enter two successive newlines to commit statements.");

    let mut ctx = ProgramContext::new();
    let mut ir_gen = match IRGenerator::new() {
        Err(e) => fatal!("{}", e),
        Ok(v) => v,
    };

    loop {
        match repl_collect_tokens() {
            Ok(tokens) => {
                let mut tokens = tokens;
                'inner: while !tokens.is_empty() {
                    let statement = match Statement::from(&mut tokens) {
                        Ok(statement) => match analyze_statement(&mut ctx, &statement) {
                            Ok(_) => {}
                            Err(e) => {
                                error!("{}", e);
                            }
                        },
                        Err(e) => {
                            error!("{}", e);
                            break 'inner;
                        }
                    };

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
    let mut line_num = 0;
    let mut out = stdout();

    out.write("----------------\n".as_bytes())?;

    loop {
        // Print a prompt based on whether this is the beginning of a new sequence or a continuation
        // of the last one.
        out.write_all(format!("{} > ", line_num).as_bytes())?;
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
