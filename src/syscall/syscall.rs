use crate::parser::arg::Argument;
use crate::parser::func_sig::FunctionSignature;
use crate::parser::r#type::Type;

/// Returns all syscall signatures.
pub fn all_syscalls() -> [FunctionSignature; 6] {
    [
        sys_exit(),
        sys_write(),
        sys_malloc(),
        sys_calloc(),
        sys_realloc(),
        sys_free(),
    ]
}

/// The `exit` system call signature. Exits the current process.
///
/// Blang:
///
///     exit(status: i64)
///
/// Libc:
///
///     void exit(int status)
pub fn sys_exit() -> FunctionSignature {
    // TODO: Update this when we have a u64 type.
    FunctionSignature::new_with_default_pos(
        "exit",
        vec![Argument::new_with_default_pos("status", Type::i64(), false)],
        None,
    )
}

/// The `write` system call signature. Tries to write `count` characters to the file descriptor from
/// the given string `buf` and returns the number of characters written.
///
/// Blang:
///
///     write(file_desc: i64, buf: string, count: i64): i64
///
/// Libc:
///
///     size_t write(int fd, const void buf[.count], size_t count)
pub fn sys_write() -> FunctionSignature {
    FunctionSignature::new_with_default_pos(
        "write",
        vec![
            Argument::new_with_default_pos("file_desc", Type::i64(), false),
            Argument::new_with_default_pos("buf", Type::string(), false),
            Argument::new_with_default_pos("count", Type::i64(), false),
        ],
        Some(Type::i64()),
    )
}

/// The `malloc` system call function signature. Allocates `size` bytes and returns a pointer to
/// the allocated memory. The memory is not initialized.
///
/// Blang:
///
///     malloc(size: usize): unsafeptr
///
/// Libc:
///
///     void *malloc(size_t size)
pub fn sys_malloc() -> FunctionSignature {
    FunctionSignature::new_with_default_pos(
        "malloc",
        vec![Argument::new_with_default_pos("size", Type::usize(), false)],
        Some(Type::unsafeptr()),
    )
}

/// The `calloc` system call function signature. allocates memory for an array of `nmemb` elements
/// of size bytes each and returns a pointer to the allocated memory. The memory is set to zero.
///
/// Blang:
///
///     calloc(nmemb: usize, size: usize): unsafeptr
///
/// Libc:
///
///     void *calloc(size_t nmemb, size_t size)
pub fn sys_calloc() -> FunctionSignature {
    FunctionSignature::new_with_default_pos(
        "calloc",
        vec![
            Argument::new_with_default_pos("nmemb", Type::usize(), false),
            Argument::new_with_default_pos("size", Type::usize(), false),
        ],
        Some(Type::unsafeptr()),
    )
}

/// The `realloc` system call function signature. Changes the size of the memory block pointed to
/// by `ptr` to `size` bytes.
///
/// Blang:
///
///     realloc(size: usize): unsafeptr
///
/// Libc:
///
///     void *realloc(size_t size)
pub fn sys_realloc() -> FunctionSignature {
    FunctionSignature::new_with_default_pos(
        "realloc",
        vec![Argument::new_with_default_pos("size", Type::usize(), false)],
        Some(Type::unsafeptr()),
    )
}

/// The `free` system call function signature. Frees the memory space pointed to by `ptr`, which
/// must have been returned by a previous call to `malloc()`, `calloc()` or `realloc()`.
///
/// Blang:
///
///     free(ptr: unsafeptr)
///
/// Libc:
///
///     void free(void *ptr)
pub fn sys_free() -> FunctionSignature {
    FunctionSignature::new_with_default_pos(
        "free",
        vec![Argument::new_with_default_pos(
            "ptr",
            Type::unsafeptr(),
            false,
        )],
        None,
    )
}
