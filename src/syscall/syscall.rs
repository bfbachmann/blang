use crate::parser::arg::Argument;
use crate::parser::func_sig::FunctionSignature;
use crate::parser::r#type::Type;

/// Returns all syscall signatures.
pub fn all_syscalls() -> [FunctionSignature; 2] {
    [sys_exit(), sys_write()]
}

/// The exit system call signature. Exits the current process.
///
/// Blang:
///
///     exit(status: i64)
///
/// Libc:
///
///     void exit(int status)
pub fn sys_exit() -> FunctionSignature {
    FunctionSignature::new_with_default_pos(
        "exit",
        vec![Argument::new("status", Type::i64())],
        None,
    )
}

/// The write system call signature. Tries to write `count` characters to the file descriptor from
/// the given string `buf` and returns the number of characters written.
///
/// Blang:
///
///     write(file_desc: i64, buf: string, count: i64): i64
///
/// Libc:
///
///     ssize_t write(int fd, const void buf[.count], size_t count);
pub fn sys_write() -> FunctionSignature {
    FunctionSignature::new_with_default_pos(
        "write",
        vec![
            Argument::new("file_desc", Type::i64()),
            Argument::new("buf", Type::string()),
            Argument::new("count", Type::i64()),
        ],
        Some(Type::i64()),
    )
}
