# Blang

_A bad language (don't use it, it's bad)._

## Example program

```
fn cumulative_sum(i64 i): i64 {
    let result = 0
    loop {
        if i == 0 {
            return result
        }

        result = result + i
        i = i - 1
    }
}

fn fib(i64 n): i64 {
    if n <= 2 {
        return 1
    }
    return fib(n-1) + fib(n-2)
}

fn main() {
    let cumulative_sum_50 = cumulative_sum(50)
    let fib_10 = fib(10)
}
```

## Useful commands

```bash
# Run tests
make test

# Compile Blang source code in file "my_code.bl" to LLVM IR.
make my_code
```

## Requirements

Rust, Cargo, and a working installation of LLVM (currently using v15.0.0).
