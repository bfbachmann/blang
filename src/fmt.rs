use std::collections::HashSet;

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

/// Returns the contents of a HashSet as a string of the form `<value1>, <value2>, ...`.
pub fn hashset_to_string<T>(set: HashSet<T>) -> String
where
    T: ToString,
{
    let mut count = set.len();
    let mut s = "".to_string();
    for v in set {
        s += v.to_string().as_str();
        if count > 1 {
            s += ", ";
        }
        count -= 1;
    }

    return s;
}
