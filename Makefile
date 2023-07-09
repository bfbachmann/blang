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
	RUST_LOG=debug cargo run -- build $@.bl
