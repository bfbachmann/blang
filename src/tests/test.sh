#!/bin/sh

set -e

# The linker/compiler tool to use to create executables from object files.
CC=${CC:-clang}

# The LLVM system compiler to use to compile LLVM IR to object files.
LLC=${LLC:-llc}

# Create a directory to store compiler output files.
output_dir="bin"
mkdir -p $output_dir

# Iterate through .bl files in tests/cases, compiling, linking, and executing each one.
for src_path in ./*.bl; do
    base_file_name=$(basename "$src_path" .bl)
    ll_path="$output_dir"/"$base_file_name".ll
    obj_path="$output_dir"/"$base_file_name".o
    exe_path="$output_dir"/"$base_file_name"

    printf "%s " "$base_file_name".bl

    # Compile Blang to LLVM IR.
    cargo -q run -- build -o "$ll_path" --unoptimized "$src_path"

    # Compile LLVM IR to an object file.
    $LLC -filetype=obj "$ll_path" -o "$obj_path" -O0

    # Link the object file with libc and create an executable.
    $CC "$obj_path" -o "$exe_path"

    # Execute the executable.
    ./"$exe_path"

    echo "PASS"
done
