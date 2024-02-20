# Set the default C compiler (we're only using it to compile object files to executables here).
# Overwrite this in your env.nu file if you'd like to use another compiler.
$env.CC = "cc"

# Source env.nu if it exists.
if ("env.nu" | path exists) {
    source "env.nu"
}

# Runs all unit and end-to-end tests.
def test [] {
    test unit
    test e2e
}

# Runs unit tests.
def "test unit" [] {
    cargo $env.CARGO_FLAGS llvm-cov -- --nocapture
}

# Runs end-to-end tests.
def "test e2e" [] {
    ls src/tests | find "_test.bl" | get name | ansi strip | par-each {|src_file|
        let exit_code = run -q $src_file
        if $exit_code == 0 {
            print $"(ansi green)PASS(ansi reset) ($src_file)"
        } else {
            print $"(ansi red)FAIL(ansi reset) ($src_file)"
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

# Compiles Blang source code.
def build [
    src: path = "source.bl"     # The path to the Blang source code to compile.
    --quiet (-q)                # Disable Blang compiler logging.
    --out (-o): path            # The path to which to write the output. Defaults to "bin/<src_stem>".
] {
    let out_path = match $out {
        "" => $"bin/($src | path parse | get stem)",
        _ => $out,
    }

    if $quiet {
        cargo $env.CARGO_FLAGS run -- build -q -o $out_path $src
    } else {
        cargo $env.CARGO_FLAGS run -- build -o $out_path $src
    }
}

# Builds and executes Blang source code.
def run [
    src: path = "."                     # The path to the Blang source code to run.
    --quiet (-q)                        # Disable Blang compiler logging.
] {
    # Build the output file path from the source path.
    let output_path = $"bin/($src | path parse | get stem)"

    # Compile Blang source code to an object file.
    if $quiet {
        build -q -o $output_path $src
    } else {
        build -o $output_path $src
    }

    # Run the executable.
    ^$"($output_path)"

    return $env.LAST_EXIT_CODE
}
