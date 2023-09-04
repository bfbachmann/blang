# Enable debug logs.
export RUST_LOG=trace

# Enable stack traces.
export RUST_BACKTRACE=full

# Run tests.
.PHONY: test
test:
	cargo llvm-cov -- --nocapture

# Generate docs.
.PHONY: docs
docs:
	cargo doc

# Automatically fix lint errors.
.PHONY: fix
fix:
	cargo fix --allow-dirty --allow-staged

# Compile Blang source code to LLVM IR.
.PHONY: %
%:
	cargo run -- build -o bin/out.ll --unoptimized $@.bl

# Inspect the object file generated by the compiler.
.PHONY: inspect
inspect:
	llvm-objdump -d out

# Creates an executable from the source code in "source.bl".
.PHONY: exec
exec: source
	@llc -filetype=obj bin/out.ll -o bin/out.o -O0 && clang bin/out.o -o bin/out

# Runs end-to-end tests. These tests compile a set of Blang source files and execute the binaries, ensuring all steps
# succeed.
.PHONY: e2e
e2e:
	@cd src/tests && ./test.sh
