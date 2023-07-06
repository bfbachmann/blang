# Blang

_A bad language (don't use it, it's bad)._

## Example program

```
fn main() {
    i64 i = 0
    loop {
        string prefix = str_concat(str_concat("Fibonacci number ", itoa(i)), " is: ")
        i64 result = fib(
            i,
            fn (i64 n): bool {
                print(str_concat("fib visitor sees n=", itoa(n)))
                return n % 2 == 0
            },
        )
        print(str_concat(prefix, itoa(result)))
        if i == 10 {
            break
        }
    }
}

// Calls `visitor_fn` with n and returns the n'th Fibonacci number.
fn fib(i64 n, fn (i64): bool visitor_fn): i64 {
    if visitor_fn(n) {
        print("visitor returned true")
    }
    if n <= 1 {
        return 1
    }
    return fib(n-1, visitor_fn) + fib(n-2, visitor_fn)
}

fn print(string s) {}

fn str_concat(string a, string b): string {
    return a
}

fn itoa(i64 i): string {
    return "fake"
}
```

## Useful commands

```bash
# Run the REPL
make repl

# Run tests
make test

# Compile Blang source code in file "my_code.bl"
make my_code
```
