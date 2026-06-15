.PHONY: fix test lint

fix:
	cargo clippy --fix --allow-dirty

test:
	cargo llvm-cov

lint:
	cargo clippy
