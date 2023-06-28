.PHONY: repl
repl:
	RUST_LOG=debug cargo run

.PHONY: test
test:
	cargo test

.PHONY: source
source:
	RUST_LOG=debug cargo run -- source
