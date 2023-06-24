use clap::{arg, Command};
use log::{debug, error, info, set_max_level, Level};
use std::fs::File;
use std::io::BufRead;
use std::io::{BufReader, Result};
use std::process;
mod ast;
mod token;

use token::Token;

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
    let matches = Command::new("dog")
        .version("0.1")
        .author("Bruno Bachmann")
        .about("A dogsh*t programming language.")
        .arg(arg!([file] "File to compile").required(true))
        .get_matches();

    // Get file name from command line argument
    let file_path = matches.get_one::<String>("file").unwrap();

    // Get a reader from the source file
    debug!("Opening file \"{}\"", file_path);
    let reader = match open_file(file_path) {
        Ok(r) => r,
        Err(err) => fatal!(r#"Error opening file "{}": {}"#, file_path, err),
    };

    // Iterate through lines from source
    info!("Compiling \"{}\"", file_path);
    for (line_num, line) in reader.lines().enumerate() {
        let line = match line {
            Ok(l) => l,
            Err(err) => fatal!("Error reading line: {}", err),
        };

        match Token::tokenize(line.as_str()) {
            Ok(tokens) => {
                debug!("Tokens on line {}: {:#?}", line_num, tokens);
            }
            Err(e) => fatal!("[{}:{}] {}", line_num, e.column, e.message),
        };
    }

    info!("Successfully compiled {}", file_path);
}

fn open_file(file_path: &str) -> Result<BufReader<File>> {
    let file = File::open(file_path)?;
    Ok(BufReader::new(file))
}
