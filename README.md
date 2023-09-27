# Blang

_A simple, statically typed, ahead-of-time compiled programming language written in Rust._

## Examples

See [src/tests](src/tests).

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
