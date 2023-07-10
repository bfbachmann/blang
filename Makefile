# Enable debug logs.
export RUST_LOG=debug

# Enable stack traces.
export RUST_BACKTRACE=1

# Run the REPL.
.PHONY: repl
repl:
	cargo run -- repl

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

# Build and run .bl source code.
.PHONY: %
%:
	cargo run -- build $@.bl
