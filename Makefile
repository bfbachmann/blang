.PHONY: repl
repl:
	RUST_LOG=debug cargo run

.PHONY: test
test:
	cargo test

.PHONY: docs
docs:
	cargo doc

.PHONY: %
%:
	RUST_LOG=debug cargo run -- $@.bl
