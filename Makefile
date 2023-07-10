# Enable debug logs.
export RUST_LOG=debug

# Enable stack traces.
export RUST_BACKTRACE=1

.PHONY: repl
repl:
	cargo run -- repl

.PHONY: test
test:
	cargo llvm-cov -- --nocapture

.PHONY: docs
docs:
	cargo doc

.PHONY: fix
fix:
	cargo fix --allow-dirty

.PHONY: %
%:
	cargo run -- build $@.bl
