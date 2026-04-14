.PHONY: lint test check

lint:
	cargo clippy --fix --allow-dirty

test:
	cargo llvm-cov

check: lint test