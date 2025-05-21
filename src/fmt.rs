use std::fmt::Display;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::time::Duration;

use crate::analyzer::error::Note;
use crate::lexer::pos::Span;
use crate::parser::SrcInfo;
use colored::{control, Colorize};

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
        print!("{}", "warning: ".custom_color(CustomColor::new(235, 227, 14)).bold());
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
pub fn display_msg(
    src_info: &SrcInfo,
    msg: &str,
    detail: Option<&String>,
    help: Option<&String>,
    span: &Span,
    is_warning: bool,
    notes: &Vec<Note>,
) {
    let path = src_info
        .file_info
        .try_get_file_path_by_id(span.file_id)
        .unwrap();

    if is_warning {
        warnln!("{}", msg.bold());
    } else {
        errorln!("{}", msg.bold());
    }

    print_source(path, span);

    let width = span.end_pos.line.to_string().len();
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

    for note in notes {
        println!("{}{}", " ".repeat(width), "|".blue().bold());
        println!(
            "{}{} {} {}",
            " ".repeat(width),
            "=".blue().bold(),
            "note:".bold(),
            note.message
        );

        let path = src_info
            .file_info
            .try_get_file_path_by_id(note.span.file_id)
            .unwrap();
        print_source(path, &note.span);
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
pub fn format_file_loc(path: &str, line: Option<u32>, col: Option<u32>) -> String {
    match (line, col) {
        (Some(l), Some(c)) if l > 0 && c > 0 => {
            format!("{} {}:{}:{}", "-->".blue().bold(), path, l, c)
        }
        _ => format!("{} {}", "-->".blue().bold(), path),
    }
}

/// Pretty-prints source code between the lines in given positions in the given file.
/// Highlights the region between `start_pos` and `end_pos` in red.
pub fn print_source(file_path: &str, span: &Span) {
    if control::SHOULD_COLORIZE.should_colorize() {
        print_source_color(file_path, span);
    } else {
        print_source_no_color(file_path, span);
    }
}

/// Pretty-prints source code between the lines in given positions in the given file.
/// Highlights the region between `start_pos` and `end_pos` in red.
fn print_source_color(file_path: &str, span: &Span) {
    let file = File::open(file_path).unwrap();
    let reader = BufReader::new(file);
    let width = span.end_pos.line.to_string().len();
    let start_pos = &span.start_pos;
    let end_pos = &span.end_pos;

    println!(
        "{}{}",
        " ".repeat(width),
        format_file_loc(file_path, Some(start_pos.line), Some(start_pos.col))
    );

    let mut mid_lines_printed = 0;
    for (i, line) in reader.lines().enumerate() {
        let line_num = i as u32 + 1;
        if line_num < start_pos.line {
            continue;
        } else if line_num > end_pos.line {
            break;
        }

        let line = line.unwrap();
        if line_num == start_pos.line && start_pos.line == end_pos.line {
            // The code only spans one line.
            let (left, right) = line.split_at(start_pos.col as usize - 1);
            let (mid, right) = right.split_at((end_pos.col - start_pos.col) as usize);
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
                mid.red().bold(),
                right
            );
        } else if line_num == start_pos.line {
            // The code spans multiple lines and this is the first.
            let (left, right) = line.split_at(start_pos.col as usize - 1);
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
                right.red().bold(),
            );
        } else if line_num == end_pos.line {
            // The code spans multiple lines and this is the last.
            let (left, right) = line.split_at(end_pos.col as usize - 1);
            println!(
                "{} {}{}",
                format!("{:>width$}|", line_num, width = width)
                    .blue()
                    .bold(),
                left.red().bold(),
                right
            );
        } else {
            mid_lines_printed += 1;

            // The code spans multiple lines and this is neither the first nor the last.
            if mid_lines_printed == 3 {
                println!("{}", ".".repeat(width + 1).blue().bold(),);
            } else if mid_lines_printed <= 1 {
                println!(
                    "{} {}",
                    format!("{:>width$}|", line_num, width = width)
                        .blue()
                        .bold(),
                    line.red().bold()
                );
            }
        }
    }
}

/// Pretty-prints source code between the lines in given positions in the given file.
/// Underlines or annotates code between the given positions.
fn print_source_no_color(file_path: &str, span: &Span) {
    let file = File::open(file_path).unwrap();
    let reader = BufReader::new(file);
    let start_pos = &span.start_pos;
    let end_pos = &span.end_pos;
    let width = end_pos.line.to_string().len();

    println!(
        "{}{}",
        " ".repeat(width),
        format_file_loc(file_path, Some(start_pos.line), Some(start_pos.col))
    );

    let mut mid_lines_printed = 0;
    for (i, line) in reader.lines().enumerate() {
        let line_num = i as u32 + 1;
        if line_num < start_pos.line {
            continue;
        } else if line_num > end_pos.line {
            break;
        }

        let line = line.unwrap();

        if line_num == start_pos.line && start_pos.line == end_pos.line {
            // The whole segment we're printing spans one line.
            let (left, right) = line.split_at(start_pos.col as usize - 1);
            let (mid, right) = right.split_at((end_pos.col - start_pos.col) as usize);
            println!("{pipe:>width$}", pipe = "|", width = width + 1);
            println!(
                "{:>width$}| {}{}{}",
                line_num,
                left,
                mid,
                right,
                width = width
            );
            println!(
                "{:>width$}| {}{}",
                " ".repeat(line_num.to_string().len()),
                " ".repeat(left.len()),
                "^".repeat(mid.len()),
                width = width
            );
        } else if line_num == start_pos.line {
            // The segment we're printing spans multiple lines, and this is the first.
            let (left, right) = line.split_at(start_pos.col as usize - 1);
            println!("{pipe:>width$}", pipe = "|", width = width + 1);
            println!("{:>width$}| {}{}", line_num, left, right, width = width);
            println!(
                "{:>width$}| {}^-- starts here",
                " ".repeat(line_num.to_string().len()),
                " ".repeat(left.len()),
                width = width
            );
        } else if line_num == end_pos.line {
            // The segment we're printing spans multiple lines, and this is the last.
            let (left, right) = line.split_at(end_pos.col as usize - 1);
            println!("{:>width$}| {}{}", line_num, left, right, width = width);
            println!(
                "{:>width$}| {}^-- ends here",
                " ".repeat(line_num.to_string().len()),
                " ".repeat(left.len() - 1),
                width = width
            );
        } else {
            // The segment we're printing spans multiple lines, and this is neither the first
            // nor the last. We only print these lines if the total segment spans more than the maximum
            // number of lines.
            mid_lines_printed += 1;

            // The code spans multiple lines and this is neither the first nor the last.
            if mid_lines_printed == 3 {
                println!("{}", ".".repeat(width + 1).blue().bold(),);
            } else if mid_lines_printed <= 1 {
                println!("{:>width$}| {}", line_num, line, width = width);
            }
        }
    }
}

/// Formats the given type hierarchy like this
///
///     A -> B -> C
pub fn hierarchy_to_string(hierarchy: &[String]) -> String {
    format_code_vec(hierarchy, " -> ")
}

/// Formats the given vector by placing `sep` between its elements, and rendering
/// each element as code using `format_code!`.
/// For example, if `sep` is ",", and `vec` is `[1, 2, 3]`, then this function
/// would return the string "`1`, `2`, `3`".
pub fn format_code_vec<T: Display>(vec: &[T], sep: &str) -> String {
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

/// Formats the given vector by placing `sep` between its elements, and rendering
/// each element as a string.
/// For example, if `sep` is ",", and `vec` is `[1, 2, 3]`, then this function
/// would return the string "1, 2, 3".
pub fn vec_to_string<T: Display>(vec: &[T], sep: &str) -> String {
    let mut s = String::from("");
    for (i, val) in vec.iter().enumerate() {
        if i == 0 {
            s.push_str(format!("{val}").as_str());
        } else {
            s.push_str(format!("{sep}{val}").as_str())
        }
    }

    s.to_string()
}

/// Returns the string representation of the given duration.
pub fn format_duration(duration: Duration) -> String {
    format!("{:.3}s", duration.as_secs_f64())
}
