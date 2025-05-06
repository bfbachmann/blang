# The Blang Programming Language

Blang is a statically-typed, ahead-of-time (AOT) compiled toy programming language that is heavily inspired by Rust. It
is
still under active development and is not intended to be a legitimate production-ready language.

**Goals**

- Safety: Unsafe code should always be explicitly opt-in.
- Simplicity: Any experienced programmer should be able to learn the core of the language within the few hours. The
  language
  should not offer programmers many ways to do the same things.
- Flexibility: Blang should be powerful and expressive without forcing any particular programming paradigms upon its
  users.

The documentation below aims to provide a quick glance at what Blang code looks like, and what it does.
The language and compiler are still very young, so they still lack some critical functionality.

<!-- TOC -->

* [Function Declarations & Calls: `fn`](#function-declarations--calls-fn)
* [Variable Declarations: `let`](#variable-declarations-let)
* [Constant Declarations: `const`](#constant-declarations-const)
* [Static Declarations: `static`](#static-declarations-static)
* [Statements as Expressions: `from`, `yield`](#statements-as-expressions-from-yield)
* [Structures: `struct`](#structures-struct)
* [Enumerations: `enum`](#enumerations-enum)
* [Tuples: `{...}`](#tuples-)
* [Arrays: `[...]`](#arrays-)
* [Implementations, Methods, and Method Calls: `impl`, `fn`](#implementations-methods-and-method-calls-impl-fn)
* [Conditionals: `if`, `else if`, `else`](#conditionals-if-elsif-else)
* [Pattern Matching: `match`](#pattern-matching-match)
* [Loops: `for`, `while`, `loop`](#loops-for-while-loop)
    * [`for` loops](#for-loops)
    * [`while` loops](#while-loops)
    * [`loop` loops](#loop-loops)
* [Pointers and Memory Access: `*_`, `*mut _`, `&`, `&mut`, `^`](#pointers-and-memory-access-_-mut-_--mut-)
* [Externs: `extern`](#externs-extern)
* [Imports: `use`](#imports-use)
* [Type Casts: `as`](#type-casts-as)
* [Generics](#generics)

<!-- TOC -->

### Function Declarations & Calls: `fn`

A regular function can be defined as follows.

```
/// This function takes an unsigned integer `n` and returns the nth number in the Fibonnaci sequence.
fn fibonacci(n: u64) -> u64 {
    if n <= 1 {
        return 1
    }

    return fibonacci(n - 1) + fibonacci(n - 2)
}
```

Functions can be nested, but nested functions don't capture data from their
enclosing scopes.

```
fn call_nested() -> int {
    fn sum(a: int, b: int) -> int {
        // You can't reference variables declared in `call_nested` from
        // inside this function.
        return a + b
    }

    return sum(1, 2)
}
```

Functions pointers can be used as values and assigned to variables.

```
fn main() {
    let func = get_fn()
    let three = func(1, 2)
}

// This function returns a function pointer.
fn get_fn() -> fn (int, int) -> int {
    fn sum(a: int, b: int) -> int {
        return a + b
    }

    return sum
}
```

### Variable Declarations: `let`

Variables can only be declared using the `let` keyword inside functions.There is currently no support for global or
module-level variables.

```
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

```
fn calculate(n: u64, double: bool, max: u64) -> u64 {
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

### Constant Declarations: `const`

Constants can be declared at the module level or inside functions using the `const` keyword.

```
// Define a const representing the number of hours in a day.
const hours_in_day = 24

// Define multiple constants, all in one `const` block.
const days_in_year = 365
const seasons = ["Spring", "Summer", "Autumn", "Winter"]

fn is_bad_day(day_in_month: int) -> bool {
    const bad_day = 13
    return day_in_month == bad_day
}
```

Like variables, constant types can be declared explicitly.

```
const bad_address: u64 = 0xdeadbeef
```

Constant values don't occupy any place in memory or program data. Instead, they are always inlined by the compiler. This
is the key difference between immutable variables (which may occupy space on the stack, and may even be copied), and
constants.

```
const x = 6 * 6

fn test() {
    // The following two statements produce identical machine code.
    do_thing(x)
    do_thing(6 * 6)
}
```

Any expression composed exclusively of constant values can be declared as a constant.

```
const my_tuple = { "this", "is my tuple", 123 / 23 - 1 }
```

### Static Declarations: `static`

Module-level static variables can be declared as follows.

```
static counter = 123

fn update_counter(value: int) {
    counter += value
}
```

Static variables can only be declared at the module level and are always considered mutable.

### Statements as Expressions: `from`, `yield`

Statements can be used as expressions using `from` and `yield`.

```
fn greet(is_morning: bool) {
    let msg = from if is_morning {
        yield "Good morning!"
    } else {
        yield "Hi!"
    }
    
    say(msg)
}
```

`from` can be used to extract values from unconditional loops (i.e. `loop`, but not `for` or `while`), exhaustive
conditionals, and closures. The `yield` statement works much like a `return`, only it passes the yielded value out of
the parent `from` block instead of returning it from a function.

### Structures: `struct`

Structure types contain values of other types that are accessible via named fields.

```
// Struct types can be declared both inside and outside functions.
struct User {
    username: str
    age: u64
}

fn main() {
    // All struct fields must be initialized explicitly.
    let user = User {
        username: "bohr"
        age: 36
    }

    // Struct values are copied automatically, like in C.
    let user_copy = user
}
```

### Enumerations: `enum`

An enum type represents one of a defined set of values.

```
// Enum types can be declared both inside and outside functions.
enum Result {
    Ok,
    Err(/* contained error message */ str)
}

fn main() {
    let result = Result::Err("failed!")

    // Enum values are copied automatically, like in C.
    let new_result = result
}
```

### Tuples: `{...}`

Tuples are like structs, except their fields are identified by index rather than by name.

```
fn main() {
    let values: { str, i64, bool } = { "thing", 1, true }

    // Tuple values are copied automatically, like in C.
    let new_values = values
    let msg = values.(0)
}
```

### Arrays: `[...]`

Arrays are stack-allocated, fixed-sized sequences of values of the same type.

```
fn main() {
    let array: [i64; 5] = [1, 2, 3, 4, 5]

    // Arrays can be declared by repeating an expression.
    let ten_zeros = [0; 10]

    // Arrays can be indexed.
    let five = array.(4)

    // Array access is bounds-checked at compile time if possible.
    let undef = array.(200)  // error: index (200) is outside of array bounds ([0:4])
}
```

### Implementations, Methods, and Method Calls: `impl`, `fn`

Blang is not object-oriented in the classical sense, but it does support the declaration of methods for existing types
using the `impl` keyword.

```
struct User {
    username: str
    age: u64
}

impl User {
    // Creates a new user with the given username and age.
    fn new(username: str, age: u64) -> User {
        return User{
            username: username
            age: age
        }
    }

    // Returns a copy of this user with the new username.
    fn with_username(self, new_username: str) -> User {
        // This is a call to a class method.
        return User.new(new_username, self .age)
    }

    fn is_senior(*self) -> bool {
        return self.age
    }
}

fn apply_discounts(user: *User) {
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

### Conditionals: `if`, `else if`, `else`

```
enum Cmp {
    Equal,
    GreaterThan,
    LessThan,
}

fn compare(a: i64, b: i64) -> Cmp {
    if a > b {
        return Cmp::GreaterThan
    } else if a < b {
        return Cmp::LessThan
    } else {
        return Cmp::Equal
    }
}
```

### Pattern Matching: `match`

`match` expressions can be used to check values for equality, or for certain patterns.
Match cases must be exhaustive.

```
enum SearchError {
    NotFound
    InvalidQuery
    Internal(uint)
}

fn handle_err(err: SearchError) {
    match err {
    case let SearchError::NotFound:
        // ...
    case let SearchError::Internal(code) if code == 1:
        handle_fatal_internal(code)
    case let SearchError::Internal(code):
        handle_internal(code)
    case:
        // handle default case
    }
}
```

### Loops: `for`, `while`, `loop`

#### `for` loops

```
fn main() {
    let mut a = [1, 2, 3]

    // Double all elements in the array.
    for let mut i = 0uint; i < 3; i = i + 1 {
        a.(i) *= 2
    }
}
```

#### `while` loops

```
fn main() {
    let mut x = 1
    while x < 100 {
        x = x * 2
    }
}
```

#### `loop` loops

```
fn main() {
    let mut x = 1

    loop {
        x = x * 2
        if x >= 100 {
            return;
        }
    }
}
```

### Pointers and Memory Access: `*_`, `*mut _`, `&`, `&mut`, `^`

Raw pointers work the same way they do in C, except that they come with immutability guarantees.

The reference operator `&` can be used to get a read-only pointer (`*_`) so some value in memory. If the value being
referenced is not already stack-allocated - for instance, if it's a constant - it will be stack allocated and
the reference operation will return the new stack address. Raw pointers of type `*_` that result from reference
operations can be read from but not written to.

The reference-mutably operator `&mut` can be used to get a read-write pointer (`*mut _`) to a value in memory.
This works like the reference operator, only the resulting pointer can be used to write to memory as well. Only mutable
values can be referenced mutably.

The dereference operator `^` can be used to retrieve a value from memory referenced by a pointer.
Dereferencing a pointer that points to an invalid or un-allocated region of memory can cause undefined behaviour.

```
fn main() {
    let mut x = 123

    // Get a pointer to `x`.
    let x_ptr = &x

    // Dereference the pointer to `x` to get its value.
    let x_copy = x^

    // Change the value of `x` via a pointer (must use `*mut`). We're only allowed
    // to get a `*mut` to `x` here because `x` itself is `mut`.
    let x_mut_ptr = &mut x
    x^ = 321
}
```

Pointer arithmetic can be done simply by indexing the pointer like one would an array.

```
fn main() {
    let ptr: * int = &[1, 2, 3] as * int
    let ptr_to_three: * int = ptr.(2) // equivalent to `ptr + 2 * sizeof int`
    let three = ptr_to_three^
}
```

### Externs: `extern`

External functions can be declared in Blang the same way they can in languages like C.

```
// Declare the `exit` system call so the linker can link it from libc.
extern fn exit(code: u64)

fn main() {
    // Exit with code 0.
    exit(0)
}
```

Externs can also be declared with custom names to link against. For example, to declare
a function `str_to_int` and have it link against `strtol`:

```
extern "strtol" fn str_to_int(start: *u8, end: *mut *u8, base: int) -> int
```

### Imports: `use`

Constants, types, and functions can be imported from other modules with `use` statements. For example, to import `Thing`
from the module at `my_project/some_dir/thing.bl`, we can do the following.

```
use "my_project/some_dir/thing.bl" {Thing}
```

Whole modules can also be imported with aliases and used as follows.

```
use "std/libc/mem.bl" @mem

fn clone_bytes(src: *u8, len: uint) -> *mut u8 {
    // Use the `malloc` function from the `mem` module.
    let dst = @mem.malloc(len)
    
    // Use the `memcpy` function from the `mem` module.
    return @mem.memcpy(dst, src, len)
}
```

These two methods of importing from a foreign module can also be combined as follows.

```
use "std/libc/io.bl" @io {stdout}
use "std/libc/proc.bl" @proc

fn die(msg: str) {
    @io.write(stdout, msg.ptr(), msg.len())
    @proc.exit(1)
}
```

### Type Casts: `as`

Values can be explicitly cast to other compatible types with the typecast operator `as`.

```
fn main() {
    // Casting between numeric types.
    let a: u32 = 10i64 as u32

    // Casting between pointers and numeric types.
    let a: i64 = &10 as i64
    let ptr: *i64 = 100 as *i64

    // Casting between pointer types.
    let x_u8_ptr = ptr.ptr()
}
```

### Generics

Struct types, enum types, and functions can be declared with generic parameters.

```
/// Contains a value of arbitrary type `T`.
struct Container[T] {
    inner_value: T
}

/// Takes any value of type `T` and returns a container that contains it.
fn new_container[T](t: T) -> Container[T] {
    return Container[T]{inner_value: t}
}
```

`impl` blocks for types that accept generic parameters inherit those parameters.

```
enum Opt[T] {
    Some(T)
    None
}

impl Opt {
    fn is_none(*self) -> bool {
        return self^ ~~ Opt[T]::None
    }
}
```

Generic parameters can have constraints in the form of specs.

```
/// Any type that can be added to itself (by reference) to produce a new value
/// of the same type.
spec Add {
    fn add(*self, other: *Self) -> Self
}

struct Vec2 {
    x: f64
    y: f64
}

// Vec2 implements the `Add` spec.
impl Vec2: Add {
    fn add(*self, other: *Vec2) -> Vec2 {
        return Vec2{
            x: self.x + other.x
            y: self.y + other.y
        }
    }
}

/// Sums any two values that implement `Add` and returns the result.
fn sum[T: Add](a: *T, b: *T) -> T {
    return a.add(b)
}
```
