#!/bin/sh

# The linker/compiler tool to use to create executables from object files.
CC=${CC:-clang}

# The LLVM system compiler to use to compile LLVM IR to object files.
LLC=${LLC:-llc}

fail() {
    echo "$1" FAIL
    exit 1
}

# Create a directory to store compiler output files.
output_dir="bin"
mkdir -p $output_dir

# Iterate through .bl files in tests, compiling, linking, and executing each one.
for src_path in ./*.bl; do
    base_file_name=$(basename "$src_path" .bl)
    ll_path="$output_dir"/"$base_file_name".ll
    obj_path="$output_dir"/"$base_file_name".o
    exe_path="$output_dir"/"$base_file_name"

    # Compile Blang to LLVM IR.
    cargo -q run -- build -o "$ll_path" "$src_path" || fail "$base_file_name".bl

    # Compile LLVM IR to an object file.
    $LLC -filetype=obj "$ll_path" -o "$obj_path" -O0 || fail "$base_file_name".bl

    # Link the object file with libc and create an executable.
    $CC "$obj_path" -o "$exe_path" || fail "$base_file_name".bl

    # Execute the executable. Pipe stdout to /dev/null to prevent output from
    # test cases from muddying the test output.
    ./"$exe_path" 1> /dev/null 2> /dev/null || fail "$base_file_name".bl

    echo "$base_file_name".bl PASS
done
