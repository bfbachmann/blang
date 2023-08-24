use std::collections::HashSet;
use std::fmt::Display;

use colored::{ColoredString, Colorize};

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
        print!("{}", "warning: ".yellow().bold());
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
pub fn format_file_loc(path: &str, line: Option<usize>, col: Option<usize>) -> ColoredString {
    match (line, col) {
        (Some(l), Some(c)) if l > 0 && c > 0 => {
            format!("--> {}:{}:{}", path, l, c).bright_black().bold()
        }
        _ => format!("--> {}", path).bright_black(),
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
