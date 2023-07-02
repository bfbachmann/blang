.PHONY: repl
repl:
	RUST_LOG=debug cargo run

.PHONY: test
test:
	cargo llvm-cov -- --nocapture

.PHONY: docs
docs:
	cargo doc

.PHONY: %
%:
	RUST_LOG=debug cargo run -- $@.bl
