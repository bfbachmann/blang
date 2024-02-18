use std::collections::HashSet;
use std::fmt::Display;
use std::fs::File;
use std::io::{BufRead, BufReader};

use colored::{Colorize};

use crate::lexer::pos::Position;

/// Prints an error message and exits with code 1.
#[macro_export]
macro_rules! fatalln {
    ($($arg:tt)*) => {{
        errorln!($($arg)*);
        process::exit(1);
    }};
}

/// Prints an error message.
#[macro_export]
macro_rules! errorln {
    ($($arg:tt)*) => {{
        print!("{}", "error: ".red().bold());
        println!($($arg)*);
    }};
}

/// Prints a warning message.
#[macro_export]
macro_rules! warnln {
    ($($arg:tt)*) => {{
        print!("{}", "warning: ".custom_color(CustomColor::new(255, 165, 0)).bold());
        println!($($arg)*);
    }};
}

/// Formats an output message where all the arguments should display as pieces of source code.
/// Example:
///
///     format_output!("invalid statement: {}", statement_ast_node)
///
/// where `statement_ast_node` looks like `let a = 1`, should expand to
/// "invalid statement: `let a = 1`", where the source code in backticks is blue (in environments
/// that support color).
#[macro_export]
macro_rules! format_code {
    ($str_lit:literal $(, $arg:expr)+ $(,)?) => {
        format!($str_lit, $(format_code!($arg)),*)
    };

    ($arg:expr) => {
        format!("`{}`", $arg).blue()
    }
}

/// Returns the contents of a HashSet as a string of the form `<value1>, <value2>, ...`.
pub fn format_hashset<T>(set: HashSet<T>) -> String
where
    T: Display,
{
    let mut count = set.len();
    let mut s = "".to_string();
    for v in set {
        s += format_code!("{}", v).as_str();
        if count > 1 {
            s += ", ";
        }
        count -= 1;
    }

    return s;
}

/// Formats the file location as a colored string.
pub fn format_file_loc(path: &str, line: Option<usize>, col: Option<usize>) -> String {
    match (line, col) {
        (Some(l), Some(c)) if l > 0 && c > 0 => {
            format!("{} {}:{}:{}", "-->".blue().bold(), path, l, c)
        }
        _ => format!("{} {}", "-->".blue().bold(), path),
    }
}

/// Pretty-prints source code between the lines in given positions in the given file.
/// Highlights the region between `start_pos` and `end_pos` in red.
pub fn print_source(file_path: &str, start_pos: &Position, end_pos: &Position) {
    let file = File::open(file_path).unwrap();
    let reader = BufReader::new(file);
    let width = end_pos.line.to_string().len();

    println!(
        "  {}",
        format_file_loc(file_path, Some(start_pos.line), Some(end_pos.line))
    );

    for (i, line) in reader.lines().enumerate() {
        let line_num = i + 1;
        if line_num < start_pos.line {
            continue;
        } else if line_num > end_pos.line {
            break;
        }

        let line = line.unwrap();
        if line_num == start_pos.line && start_pos.line == end_pos.line {
            let (left, right) = line.split_at(start_pos.col - 1);
            let (mid, right) = right.split_at(end_pos.col - start_pos.col);
            println!(
                "{pipe:>width$}",
                pipe = "|".blue().bold(),
                width = width + 1
            );
            println!(
                "{} {}{}{}",
                format!("{:>width$}|", line_num, width = width)
                    .blue()
                    .bold(),
                left,
                mid.on_bright_red(),
                right
            );
        } else if line_num == start_pos.line {
            let (left, right) = line.split_at(start_pos.col - 1);
            println!(
                "{pipe:>width$}",
                pipe = "|".blue().bold(),
                width = width + 1
            );
            println!(
                "{} {}{}",
                format!("{:>width$}|", line_num, width = width)
                    .blue()
                    .bold(),
                left,
                right.on_bright_red(),
            );
        } else if line_num == end_pos.line {
            let (left, right) = line.split_at(end_pos.col - 1);
            println!(
                "{} {}{}",
                format!("{:>width$}|", line_num, width = width)
                    .blue()
                    .bold(),
                left.on_bright_red(),
                right
            );
        } else {
            println!(
                "{} {}",
                format!("{:>width$}|", line_num, width = width)
                    .blue()
                    .bold(),
                line.on_bright_red()
            );
        }
    }
}

/// Formats the given type hierarchy like this
///
///     A -> B -> C
pub fn hierarchy_to_string(hierarchy: Vec<String>) -> String {
    let mut s = String::from("");
    for (i, type_name) in hierarchy.iter().enumerate() {
        if i == 0 {
            s.push_str(format_code!(type_name).to_string().as_str());
        } else {
            s.push_str(format_code!(" -> {}", type_name).to_string().as_str())
        }
    }

    s.to_string()
}
