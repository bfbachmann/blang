# Set the default LLVM IR compiler.
# Overwrite this in your env.nu file if you'd like to use another compiler.
$env.IR_COMPILER = "clang"

# Source env.nu if it exists.
if ("env.nu" | path exists) {
    source "env.nu"
}

# Runs all unit and end-to-end tests.
def test [] {
    unittest
    e2etest
}

# Runs unit tests.
def unittest [] {
    cargo llvm-cov -- --nocapture
}

# Runs end-to-end tests.
def e2etest [] {
    cd src/tests
    ./test.sh
}

# Generates documentation.
def docs [] {
    cargo doc
}

# Automatically fixes rustfmt lint errors.
def fix [] {
    cargo fix --allow-dirty --allow-staged
}

# Runs the Blang compiler "check" command which performs static analysis on the given
# Blang source code and dumps the resulting AST to `bin/dump.txt`.
def check [
    src: path = "source.bl"     # The path to the Blang source code to check.
] {
    cargo run -- check --dump bin/dump.txt ($src)
}

# Compiles Blang source code to LLVM IR.
def build [
    src: path = "source.bl"     # The path to the Blang source code to compile.
] {
    cargo run -- build -o bin/out.ll ($src)
}

# Builds and executes Blang source code.
def run [
    src: path = "source.bl"     # The path to the Blang source code to run.
    ...cflags: string           # Additional flags to pass to the LLVM IR compiler (clang).
] {
    # Compile Blang source code to LLVM IR.
    build $src

    # Compile the LLVM IR to an executable.
    ^$"($env.IR_COMPILER)" bin/out.ll -o bin/out ($env.CFLAGS) ($cflags | str join)

    # Run the executable.
    ./bin/out
}
