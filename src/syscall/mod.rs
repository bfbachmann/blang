//! The Blang syscall module exposes a set of function signatures that match libc functions. These
//! function signatures are provided to the analyzer to be checked and enriched, and are ultimately
//! included in the program by the compiler as `extern` functions so they can be linked with libc
//! when the object file created by the compiler is linked.

pub mod syscall;
