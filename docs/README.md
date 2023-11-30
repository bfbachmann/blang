# The Blang Programming Language

Blang is a statically-typed, ahead-of-time (AOT) compiled programming language that is heavily inspired by Rust. It is 
still under active development.

## Goals

- Safety: Unsafe code should always be explicitly opt-in.
- Simplicity: Any experienced programmer should be able to learn the core of the language within the few hours. The language
should not offer programmers many ways to do the same things.
- Flexibility: Blang should be powerful and expressive without forcing any particular programming paradigms upon its users.

## Language Features At a Glance

The documentation below aims to provide a quick glance at what Blang code looks like, and what it does.
The language and compiler are still very young, so they still lack some critical functionality.

### Statements

Statements in Blang are pieces of code that do not necessarily yield any value (as opposed to expressions, which always
yield some value). Listed below are the kinds of statements the Blang compiler understands.

#### Function Declarations & Calls

A regular function can be defined as follows.

```rust
/// This function takes an unsigned integer `n` and returns the nth number in the Fibonnaci sequence. 
fn fibonacci(n: u64) ~ u64 {
    if n <= 1 {
        return 1
    }
    
    return fibonacci(n-1) + fibonacci(n-2)
}
```

#### Variable Declarations

Variables can only be declared using the `let` keyword inside functions (i.e. there is currently no support for global or 
module-level variables).

```rust
fn demo() {
    // Declare a variable named `x` with the value 2.
    // Since the type type of `x` was not specified, it is assumed here to be `i64`. 
    let x = 2
    
    // Declare a variable named `y` with the value 10.
    // Since the type is specified as `u64` here, the expression assigned to the variable will be coerced to a `u64`.
    let y: u64 = 123_234 / 3
}
```

Variables declared this way are always either stack-allocated or inlined depending on how they're structured and used.

By default, all variables are immutable. To declare a mutable variable, use the `mut` modifier.

```rust
fn calculate(n: u64, double: bool, max: u64) ~ u64 {
    let mut result = n

    if double {
        result = result * 2
    }

    if result > max {
        return max
    }

    return result
}
```

#### Constant Declarations

Constants can be declared at the module level or inside functions using the `const` keyword. 

```rust
// Define a const representing the number of hours in a day.
const HOURS_IN_DAY = 24

// Define multiple constants, all in one `const` block.
const {
    DAYS_IN_YEAR = 365
    SEASONS = ["Spring", "Summer", "Autumn", "Winter"]
}

fn is_bad_day(day_in_month: u64) ~ bool {
    const BAD_DAY = 13
    return day_in_month == BAD_DAY
}
```

Like variables, constant types can be declared explicitly.

```rust
const DEFAULT_BALANCE: u64 = 10_000
```

Constant values don't occupy any place in memory or program data. Instead, they are always inlined by the compiler. This
is the key difference between immutable variables (which may occupy space on the stack, and may even be copied), and constants.

```rust
const X = 6 * 6

fn test() {
    // The following two statements produce identical machine code.
    do_thing(X)
    do_thing(6 * 6) 
    
}
```

Any expression composed exclusively of constant values can be declared as a constant.

```rust
const MY_TUPLE = {"this", "is my tuple", 123 / 23 - 1}
```

#### Type Declarations

Types can be declared at the module level and within functions.

```rust
struct User {
    username: str
    age: u64
}

enum Result {
    Ok
    Err(str) // Enums variants can contain other types.
}
```

#### Implementations, Methods, and Method Calls

Blang is not object-oriented in the classical sense, but it does support the declaration of methods for existing types
using the `impl` keyword.

```rust
struct User {
    username: str
    age: u64
}

impl User {
    // Creates a new user with the given username and age.
    fn new(username: str, age: u64) ~ User {
        return User{
            username: username
            age: age
        }
    }
    
    // Returns a copy of this user with the new username.
    fn with_username(self, new_username: str) ~ User {
        // This is a call to a class method.
        return User.new(new_username, self.age)
    }

    fn is_senior(self) ~ bool {
        return self.age
    }
}

fn apply_discounts(user: User) {
    // This is what a method call looks like.
    if user.is_senior() {
        // ... 
    } else {
        // ...    
    }
}
```

Arbitrarily many `impl` blocks can be declared for the same type. This way, logic associated with a type can easily
be split up over multiple files.

#### Control Flow

TODO

#### Externs

TODO

#### Pointers and Memory Access

TODO
