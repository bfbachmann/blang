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
def "test unit" [] {
    cargo $env.CARGO_FLAGS llvm-cov -- --nocapture
}

# Runs end-to-end tests.
def "test e2e" [] {
    mkdir src/tests/bin
    ls src/tests | find .bl | get name | ansi strip | each {|src_file|
        print -n $"test ($src_file)... "

        let exit_code = run $src_file
        if $exit_code == 0 {
            print $"(ansi green)ok(ansi reset)"
        } else {
            print $"(ansi red)fail(ansi reset)"
        }
    }
}

# Generates documentation.
def docs [] {
    cargo $env.CARGO_FLAGS doc
}

# Automatically fixes rustfmt lint errors.
def fix [] {
    cargo $env.CARGO_FLAGS fix --allow-dirty --allow-staged
}

# Runs the Blang compiler "check" command which performs static analysis on the given
# Blang source code and dumps the resulting AST to `bin/dump.txt`.
def check [
    src: path = "source.bl"     # The path to the Blang source code to check.
] {
    cargo $env.CARGO_FLAGS run -- check --dump bin/dump.txt ($src)
}

# Compiles Blang source code to LLVM IR.
def build [
    src: path = "source.bl"     # The path to the Blang source code to compile.
] {
    cargo $env.CARGO_FLAGS run -- build -o bin/out.ll ($src)
}

# Builds and executes Blang source code.
def run [
    src: path = "source.bl"             # The path to the Blang source code to run.
    ...cflags: string                   # Additional flags to pass to the LLVM IR compiler (clang).
] {
    # Compile Blang source code to LLVM IR.
    build $src

    # Compile the LLVM IR to an executable.
    ^$"($env.IR_COMPILER)" bin/out.ll -o bin/out ($env.CFLAGS) ($cflags | str join)

    # Run the executable.
    ./bin/out

    return $env.LAST_EXIT_CODE
}
