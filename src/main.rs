use clap::{arg, Command};
use std::fs::File;
use std::io::{Result, BufReader};
use std::io::BufRead;
use std::process;
use log::{Level, set_max_level, info, debug, error};
use regex::Regex;
use lazy_static::lazy_static;

macro_rules! fatal {
    ($($arg:tt)*) => {{
        error!($($arg)*);
        process::exit(1);
    }};
}

#[derive(Debug)]
enum Token {
    Variable(String),
    Int(i64),
    Plus,
    Minus,
    Let,
}

impl Token {
    fn parse_first(segment: &str) -> Option<(Token, usize)> {
        // debug!("Checking segment {}", segment);
        let mut result = None;
        for (i, _) in segment.char_indices() {
            // debug!("Checking subsegment {}", &segment[..=i]);
            match &segment[..=i] {
                "+" => { 
                    return Some((Token::Plus, i));
                },
                "-" => { 
                    return Some((Token::Minus, i));
                },
                "let" => { 
                    return Some((Token::Let, i));
                },
                other => {
                    if let Some(int_token) = Token::parse_int(&other) {
                        // This segment is an Int. If so, we record it but continue
                        // searching as it may contain more digits.
                        result = Some((int_token, i));
                    } else if let Some(var_token) = Token::parse_variable_name(&other) {
                        // This segment is a Variable. If so, we record it but continue
                        // searching as it may contain more characters.
                        result = Some((var_token, i));
                    } else if let Some(_) = result {
                        // At this point we know that the segment ending at the
                        // current index is invalid, so since we already have a
                        // valid token, we should return it.
                        return result;
                    }
                },
            };
        }

        result
    }

    fn parse_int(segment: &str) -> Option<Token> {
        match segment.parse::<i64>() {
            Ok(i) => Some(Token::Int(i)),
            Err(_) => None,
        }
    }

    fn parse_variable_name(segment: &str) -> Option<Token> {
        // Use lazy_static to avoid compiling the same regex twice
        lazy_static! {
            static ref RE: Regex = Regex::new(r"[a-zA-Z_]+[a-zA-Z0-9_]*").unwrap();
        }

        match RE.is_match(segment) {
            true => Some(Token::Variable(String::from(segment))),
            false => None,
        }
    }
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
        Err(err) => fatal!("Error opening file \"{}\": {}", file_path, err),
    };

    // Iterate through lines from source
    info!("Compiling \"{}\"", file_path);
    for (line_num, line) in reader.lines().enumerate() {
        let line = match line {
            Ok(l) => l,
            Err(err) => fatal!("Error reading line: {}", err),
        };

        let mut tokens = vec![];
        let segments: Vec<&str> = line.split_whitespace().collect();
        for seg in segments {
            let mut seg_remaining = String::from(seg);

            while !seg_remaining.is_empty() {
                if let Some((token, token_len)) = Token::parse_first(&seg_remaining) {
                    // debug!("Found token {:#?} ending on index {}", token, token_len);
                    tokens.push(token);
                    seg_remaining = String::from(&seg_remaining[token_len+1..]);
                } else {
                    fatal!("[{}] Invalid token: {}", line_num, seg);
                }
            }
        }

        debug!("Tokens on line {}: {:#?}", line_num, tokens);
    }
}

fn open_file(file_path: &str) -> Result<BufReader<File>> {
    let file = File::open(file_path)?;
    Ok(BufReader::new(file))
}
