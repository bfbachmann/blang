extern crate core;

use std::collections::VecDeque;
use std::fs::File;
use std::io::{stdin, stdout, BufReader, Error, ErrorKind, Result, Write};
use std::process;

use clap::{arg, Command};
use log::{error, info, set_max_level, Level};

use lexer::token::Token;
use parser::program::Program;
use parser::statement::Statement;

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
    // Set log level
    env_logger::init();
    set_max_level(Level::Debug.to_level_filter());

    // Define command
    let matches = Command::new("blang")
        .version("0.1")
        .author("Bruno Bachmann")
        .about("A bad programming language.")
        .arg(arg!([file] "File to compile"))
        .get_matches();

    // Get file name from command line argument. If there is none, start a repl.
    match matches.get_one::<String>("file") {
        Some(file_path) => compile(file_path),
        None => repl(),
    }
}

/// Opens the file at the given path and returns a reader for it.
fn open_file(file_path: &str) -> Result<BufReader<File>> {
    let file = File::open(file_path)?;
    Ok(BufReader::new(file))
}

/// Compiles a file.
fn compile(file_path: &str) {
    // Get a reader from the source file
    let reader = match open_file(file_path) {
        Ok(r) => r,
        Err(err) => fatal!(r#"Error opening file "{}": {}"#, file_path, err),
    };

    // Break the file into tokens.
    let mut tokens = match Token::tokenize_file(reader) {
        Ok(tokens) => tokens,
        Err(e) => fatal!("{}", e),
    };

    // Parse the program.
    match Program::from(&mut tokens) {
        Ok(prog) => dbg!(prog),
        Err(e) => fatal!("{}", e),
    };
}

/// Starts a REPL. The REPL will prompt for input and try to interpret it as a statement, then
/// print the result of the statement.
fn repl() {
    info!("Starting REPL.");
    info!("Use ^C to exit. Enter two successive newlines to commit a new statement.");
    loop {
        match repl_collect_tokens() {
            Ok(tokens) => {
                let mut tokens = tokens;
                match Statement::from(&mut tokens) {
                    Ok(statement) => {
                        dbg!(statement);
                    }
                    Err(e) => error!("{}", e),
                };
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

    loop {
        // Print a prompt based on whether this is the beginning of a new sequence or a continuation
        // of the last one.
        match line_num {
            0 => stdout().write_all(b" > ")?,
            _ => stdout().write_all(b" >> ")?,
        }
        stdout().flush()?;
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
