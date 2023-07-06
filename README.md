# Blang

_A bad language (don't use it, it's bad)._

## Example program

```
fn main() {
    int i = 0
    loop {
        string prefix = str_concat(str_concat("Fibonacci number ", itoa(i)), " is: ")
        int result = fib(
            i,
            fn (int n): bool {
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
fn fib(int n, fn (int): bool visitor_fn): int {
    if visitor_fn(n) {
        print("visitor returned true")
    }
    if n <= 1 {
        return 1
    }
    return fib(n-1, visitor_fn) + fib(n-2, visitor_fn)
}

fn print(string s) {
    // Do IO...
}

fn str_concat(string a, string b): string {
    return a
}

fn itoa(int i): string {
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
