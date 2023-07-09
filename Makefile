export RUST_LOG=debug
export RUST_BACKTRACE=1

.PHONY: repl
repl:
	RUST_LOG=debug cargo run -- repl

.PHONY: test
test:
	cargo llvm-cov -- --nocapture

.PHONY: docs
docs:
	cargo doc

.PHONY: %
%:
	cargo run -- build $@.bl
