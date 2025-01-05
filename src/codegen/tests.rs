#[cfg(test)]
mod tests {
    use crate::analyzer::analyze::analyze_modules;
    use crate::codegen::program::{
        generate, init_default_host_target, CodeGenConfig, OutputFormat,
    };
    use crate::lexer::lex::lex;
    use crate::lexer::stream::Stream;
    use crate::mono_collector::mono_prog;
    use crate::parser::module::Module;
    use std::path::PathBuf;

    fn assert_compiles(code: &str) {
        let tokens = lex(code).expect("should not error");
        let module = Module::from("test", &mut Stream::from(tokens)).expect("should not error");
        let target_machine = init_default_host_target().unwrap();
        let config = CodeGenConfig::new_default(
            target_machine,
            PathBuf::from("/dev/null"),
            OutputFormat::Object,
        );
        let analysis = analyze_modules(vec![module], config);
        let prog = mono_prog(analysis);
        generate(prog).expect("should not error");
    }

    #[test]
    fn basic_program() {
        assert_compiles(
            r#"
            fn main() {
                let val = other(2, 10)
                fib(val)

                let hi = "hello world!!"
                str_stuff("test")
            }

            fn thing(b: bool) -> bool {
                let a = true
                return !a || b
            }

            fn other(a: i64, b: i64) -> i64 {
                return a * b + a / 2 - 1
            }

            fn fib(n: i64) -> i64 {
                if n < 2 {
                    return 1
                }

                return fib(n-1) + fib(n-2)
            }

            fn do_thing(a: i64) -> i64 {
                let mut result = 5
                let mut mut_a = a
                loop {
                    if mut_a < 10 {
                        loop {
                            result = result + 1
                            if result > 100 {
                                mut_a = mut_a / 2
                                break
                            } else {
                                continue
                            }
                        }
                    }

                    return mut_a * result
                }
            }

            fn cum_sum(n: i64) -> i64 {
                let mut i = 1
                let mut result = 0
                loop {
                    if i >= n {
                        return result
                    }

                    {{
                        result = result + i
                        i = i + 1
                    }}
                }
            }

            fn str_stuff(s: str) -> str {
                return "test"
            }
        "#,
        );
    }

    #[test]
    fn struct_init() {
        assert_compiles(
            r#"
            struct Person {
                name: str,
                age: i64,
                do_thing: fn(str) -> i64,
            }

            fn new_person(name: str, age: i64) -> Person {
                return Person{
                    name: name,
                    age: age,
                    do_thing: test
                }
            }

            fn test(s: str) -> i64 {
                return 1
            }

            fn main() {
                let p = Person{
                    name: "test",
                    age: 12,
                    do_thing: test,
                }

                let pp = new_person("guy", 32)
            }
        "#,
        );
    }

    #[test]
    fn struct_pass_by_value() {
        assert_compiles(
            r#"
            struct Person {
                age: i64,
            }

            fn is_old(p: Person) -> bool {
                let p = Person{age: 100}
                return false
            }

            fn main() {
                let mut p = Person{age: 10}
                is_old(p)
                p = Person{age: 1}
            }
        "#,
        );
    }

    #[test]
    fn uses_externs() {
        assert_compiles(
            r#"
            extern fn write(fd: i64, msg: str, len: i64)
            extern fn exit(code: i64)

            fn main() {
                write(1, "Hello World!", 13)
                exit(0)
            }
       "#,
        );
    }

    #[test]
    fn valid_type_def_cycle() {
        assert_compiles(
            r#"
            struct A {
                count: i64,
                f: fn(A),
            }

            fn do_thing(a: A) {}

            fn new_a(count: i64) -> A {
                return A {
                    count: count,
                    f: do_thing,
                }
            }
            "#,
        )
    }

    #[test]
    fn infinite_loop() {
        assert_compiles(
            r#"
            fn main() {
                loop {}

                let a = 1
            }
            "#,
        );
    }

    #[test]
    fn chained_method_calls() {
        assert_compiles(
            r#"
            struct Value {
                inner: int
            }
            impl Value {
                fn add(self, v: i64) -> Value { return Value{inner: self.inner + v } }
                fn sub(self, v: i64) -> Value { return Value{inner: self.inner - v } }
            }
            fn main() {
                let i = Value{inner: 1i64}
                let v = i.add(10).sub(50).sub(2).add(-24)
                i.sub(10).add(1)
            }
            "#,
        );
    }

    #[test]
    fn enums() {
        assert_compiles(
            r#"
            struct S {
                i: i64
                b: bool
                s: str
            }

            enum E {
                One
                Two(i64)
                Three(bool)
                Four(S)
            }

            fn main() {
                let e_one = E::One
                let e_two = E::Two(-42)
                let e_three = E::Three(true)
                let e_four = E::Four(S{
                    i: 12
                    b: false
                    s: "test"
                })
            }
            "#,
        );
    }

    #[test]
    fn function_generic_using_specs() {
        assert_compiles(
            r#"
            extern fn write(fd: i64, msg: str, len: i64) -> i64

            spec Task {
                fn run(self) -> bool
            }

            struct PrintTask {
                msg: str
            }

            impl PrintTask: Task {
                fn run(self) -> bool {
                    write(1, self.msg, 100)
                    return true
                }
            }

            fn run_task[T: Task](task: T) -> bool {
                return task.run()
            }

            fn main() {
                let task = PrintTask{msg: "hello world"}
                run_task[PrintTask](task)
            }
        "#,
        )
    }

    #[test]
    fn functions_as_values() {
        assert_compiles(
            r#"
            extern fn exit(code: i64)

            fn assert(b: bool, code: i64) {
                if !b {
                    exit(code)
                }
            }

            struct Calculator {
                calc_fn: fn (i64, i64) -> i64
                accumulator: i64
            }

            impl Calculator {
                fn new(f: fn (i64, i64) -> i64) -> Calculator {
                    return Calculator{
                        calc_fn: f
                        accumulator: 0
                    }
                }

                fn update(mut self, value: i64) -> Calculator {
                    let func = self.calc_fn
                    self.accumulator = func(self.accumulator, value)
                    return self
                }

                fn with_calc_fn(mut self, f: fn (i64, i64) -> i64) -> Calculator {
                    self.calc_fn = f
                    return self
                }
            }

            fn add(a: i64, b: i64) -> i64 {
                return a + b
            }

            fn mul(a: i64, b: i64) -> i64 {
                return a * b
            }

            fn main() {
                let calc = Calculator.new(add)
                let mut result = calc
                    .update(5)
                    .update(-12)
                    .update(14)
                    .with_calc_fn(mul)
                    .update(10)

                assert(result.accumulator == 70, 1)

                exit(0)
            }
        "#,
        )
    }

    #[test]
    fn valid_type_cast() {
        assert_compiles(
            r#"
            fn main() {
                let a = 10i64
                let b = a as u64
                let c: u64 = b + 8i64 as u64
            }
        "#,
        )
    }

    #[test]
    fn generic_return_types() {
        assert_compiles(
            r#"
            spec Default {
                fn default() -> Self
            }

            fn default[T: Default]() -> T {
                return T.default()
            }

            struct Thing {
                value: int
            }

            impl Thing: Default {
                fn default() -> Thing {
                    return Thing{value: 0}
                }
            }

            struct MyStruct {
                thing: Thing
            }

            impl MyStruct: Default {
                fn default() -> MyStruct {
                    return MyStruct{
                        thing: default[Thing]()
                    }
                }
            }

            fn main() {
                let my_struct = default[MyStruct]()
            }
            "#,
        )
    }

    #[test]
    fn param_fn_used_as_var() {
        assert_compiles(
            r#"
            fn apply[T](f: fn (T) -> T, arg: T) -> T {
                return f(arg)
            }

            fn double(v: i64) -> i64 {
                return v * 2
            }

            fn main() {
                let result: i64 = apply[i64](double, 1)
            }
            "#,
        )
    }

    #[test]
    fn enum_comparison() {
        assert_compiles(
            r#"
            enum Result { Ok, Err }

            fn main() {
                let a = Result::Ok ~~ Result::Err
                let r = Result::Err

                let b = r !~ Result::Ok
            }
            "#,
        )
    }
}
