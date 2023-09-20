# Blang

_A simple, statically typed, ahead-of-time compiled programming language written in Rust._

## Example program

```rust
// Returns the sum of all integers from 1 to `n` (inclusive).
fn cumulative_sum(mut n: i64): i64 {
    let mut result = 0
    loop {
        if n == 0 {
            return result
        }

        result = result + n
        n = n - 1
    }
}

// Returns the `n`th Fibonacci number.
fn fib(n: i64): i64 {
    if n <= 2 {
        return 1
    }
    return fib(n-1) + fib(n-2)
}

fn main() {
    let cumulative_sum_50 = cumulative_sum(50)
    let fib_10 = fib(10)
}
```

For more examples, see [src/tests](src/tests).

## Compiler CLI

```
The Blang programming language.

Usage: blang <COMMAND>

Commands:
  build  Compile Blang source code to LLVM IR
  check  Perform static analysis only
  help   Print this message or the help of the given subcommand(s)

Options:
  -h, --help     Print help
  -V, --version  Print version
```

## Development Utilities

See [Makefile](Makefile).

## Development Requirements

Rust, Cargo, and a working installation of LLVM (currently using v15.0.0).
