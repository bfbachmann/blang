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
    ls src/tests | find .bl | get name | ansi strip | par-each {|src_file|
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
    --out (-o): path            # The path to which to write the output. Defaults to "bin/<src_stem>.o".
] {
    let out_path = match $out {
        "" => $"bin/($src | path parse | get stem).o",
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
    ...cflags: string                   # Additional flags to pass to the LLVM IR compiler (clang).
] {
    # Build the object file output path from the source path.
    let obj_path  = match $src {
        "." => "bin/all.o",
        _ => $"bin/($src | path parse | get stem).o",
    }

    # Compile Blang source code to an object file.
    if $quiet {
        build -q -o $obj_path $src
    } else {
        build -o $obj_path $src
    }

     # Build the executable path from the source path.
    let exe_path = match $src {
        "." => "bin/all",
        _ => $"bin/($src | path parse | get stem)",
    }

    # Compile the object file to an executable.
    ^$"($env.CC)" $obj_path -o $exe_path ($env.CFLAGS) ($cflags | str join)

    # Run the executable.
    ^$"($exe_path)"

    return $env.LAST_EXIT_CODE
}
