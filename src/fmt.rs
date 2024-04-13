use std::fmt::Display;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::time::Duration;

use colored::{control, Colorize};

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
        use colored::Colorize;
        print!("{}", "error: ".red().bold());
        println!($($arg)*);
    }};
}

/// Prints a warning message.
#[macro_export]
macro_rules! warnln {
    ($($arg:tt)*) => {{
        use colored::{CustomColor, Colorize};
        print!("{}", "warning: ".custom_color(CustomColor::new(255, 165, 0)).bold());
        println!($($arg)*);
    }};
}

/// Formats an output message where all the arguments should display as pieces of source code.
/// Example:
///
///     format_code!("invalid statement: {}", statement_ast_node)
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
        {
            use colored::Colorize;
            format!("`{}`", $arg).blue()
        }
    }
}

/// Displays the given error/warning message in a user-friendly form.
pub fn display_err(
    msg: &str,
    detail: Option<&String>,
    help: Option<&String>,
    path: &str,
    start: &Position,
    end: &Position,
    is_warning: bool,
) {
    if is_warning {
        warnln!("{}", msg.bold());
    } else {
        errorln!("{}", msg.bold());
    }

    print_source(path, start, end);

    let width = end.line.to_string().len();
    if let Some(detail_msg) = detail {
        println!("{}{}", " ".repeat(width), "|".blue().bold());
        println!(
            "{}{} {} {}",
            " ".repeat(width),
            "=".blue().bold(),
            "note:".bold(),
            detail_msg
        );
    }

    if let Some(help_msg) = help {
        if detail.is_none() {
            println!("{}{}", " ".repeat(width), "|".blue().bold());
        }
        println!(
            "{}{} {} {}",
            " ".repeat(width),
            "=".blue().bold(),
            "help:".green().bold(),
            help_msg
        );
    }

    println!();
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
    if control::SHOULD_COLORIZE.should_colorize() {
        print_source_color(file_path, start_pos, end_pos);
    } else {
        print_source_no_color(file_path, start_pos, end_pos);
    }
}

/// Pretty-prints source code between the lines in given positions in the given file.
/// Highlights the region between `start_pos` and `end_pos` in red.
fn print_source_color(file_path: &str, start_pos: &Position, end_pos: &Position) {
    let file = File::open(file_path).unwrap();
    let reader = BufReader::new(file);
    let width = end_pos.line.to_string().len();

    println!(
        "{}{}",
        " ".repeat(width),
        format_file_loc(file_path, Some(start_pos.line), Some(start_pos.col))
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

/// Pretty-prints source code between the lines in given positions in the given file.
/// Underlines or annotates code between the given positions.
fn print_source_no_color(file_path: &str, start_pos: &Position, end_pos: &Position) {
    let file = File::open(file_path).unwrap();
    let reader = BufReader::new(file);
    let width = end_pos.line.to_string().len();

    println!(
        "{}{}",
        " ".repeat(width),
        format_file_loc(file_path, Some(start_pos.line), Some(start_pos.col))
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
            // The whole segment we're printing spans one line.
            let (left, right) = line.split_at(start_pos.col - 1);
            let (mid, right) = right.split_at(end_pos.col - start_pos.col);
            println!("{pipe:>width$}", pipe = "|", width = width + 1);
            println!(
                "{} {}{}{}",
                format!("{:>width$}|", line_num, width = width),
                left,
                mid,
                right
            );
            println!(
                "{} {}{}",
                format!(
                    "{:>width$}|",
                    " ".repeat(line_num.to_string().len()),
                    width = width
                ),
                " ".repeat(left.len()),
                "^".repeat(mid.len()),
            );
        } else if line_num == start_pos.line {
            // The segment we're printing spans multiple lines, and this is the first.
            let (left, right) = line.split_at(start_pos.col - 1);
            println!("{pipe:>width$}", pipe = "|", width = width + 1);
            println!(
                "{} {}{}",
                format!("{:>width$}|", line_num, width = width),
                left,
                right,
            );
            println!(
                "{} {}^-- starts here",
                format!(
                    "{:>width$}|",
                    " ".repeat(line_num.to_string().len()),
                    width = width
                ),
                " ".repeat(left.len()),
            );
        } else if line_num == end_pos.line {
            // The segment we're printing spans multiple lines, and this is the last.
            let (left, right) = line.split_at(end_pos.col - 1);
            println!(
                "{} {}{}",
                format!("{:>width$}|", line_num, width = width),
                left,
                right
            );
            println!(
                "{} {}^-- ends here",
                format!(
                    "{:>width$}|",
                    " ".repeat(line_num.to_string().len()),
                    width = width
                ),
                " ".repeat(left.len() - 1),
            );
        } else {
            // The segment we're printing spans multiple lines, and this is neither the first
            // nor the last. We only print these lines if the total segment spans more than the maximum
            // number of lines.
            println!(
                "{} {}",
                format!("{:>width$}|", line_num, width = width),
                line
            );
        }
    }
}

/// Formats the given type hierarchy like this
///
///     A -> B -> C
pub fn hierarchy_to_string(hierarchy: &Vec<String>) -> String {
    return format_vec(hierarchy, " -> ");
}

/// Formats the given vector by placing `sep` between its elements.
/// For example, if `sep` is ",", and `vec` is `[1, 2, 3]`, then this function
/// would return the string `"1, 2, 3"`.
pub fn format_vec<T: Display>(vec: &Vec<T>, sep: &str) -> String {
    let mut s = String::from("");
    for (i, val) in vec.iter().enumerate() {
        if i == 0 {
            s.push_str(format_code!(val).to_string().as_str());
        } else {
            s.push_str(
                format!("{}{}", sep, format_code!("{}", val))
                    .to_string()
                    .as_str(),
            )
        }
    }

    s.to_string()
}

/// Returns the string representation of the given duration.
pub fn format_duration(duration: Duration) -> String {
    format!("{:.2}s", duration.as_secs_f64())
}
