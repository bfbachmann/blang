#[cfg(test)]
mod tests {
    use std::path::Path;

    use crate::analyzer::analyze::analyze_sources;
    use crate::codegen::program::{generate, OutputFormat};
    use crate::lexer::lex::lex;
    use crate::lexer::stream::Stream;
    use crate::parser::source::Source;

    fn assert_compiles(code: &str) {
        let mut char_stream = Stream::from(code.chars().collect());
        let tokens = lex(&mut char_stream).expect("should not error");
        let source = Source::from("", &mut Stream::from(tokens)).expect("should not error");
        let analysis = analyze_sources(vec![source]);
        generate(
            analysis
                .analyzed_sources
                .into_iter()
                .map(|a| a.source)
                .collect(),
            analysis.type_store,
            None,
            OutputFormat::Object,
            Path::new("/dev/null"),
            true,
        )
        .expect("should not error");
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
            
            fn thing(b: bool) ~ bool {
                let a = true
                return !a or b
            }
            
            fn other(a: i64, b: i64) ~ i64 {
                return a * b + a / 2 - 1
            }
            
            fn fib(n: i64) ~ i64 {
                if n < 2 {
                    return 1
                }
                
                return fib(n-1) + fib(n-2)
            }
            
            fn do_thing(a: i64) ~ i64 {
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
            
            fn cum_sum(n: i64) ~ i64 {
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
            
            fn str_stuff(s: str) ~ str {
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
                do_thing: fn(str) ~ i64,
            }
            
            fn new_person(name: str, age: i64) ~ Person {
                return Person{
                    name: name,
                    age: age,
                    do_thing: test
                }
            }
            
            fn test(s: str) ~ i64 {
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
            
            fn is_old(p: Person) ~ bool {
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
            extern {
                fn exit(code: i64)
            }
            
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
            
            fn do(a: A) {}
            
            fn new_a(count: i64) ~ A {
                return A {
                    count: count,
                    f: do,
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
            impl i64 {
                fn add(self, v: i64) ~ i64 { return self + v }
                fn sub(self, v: i64) ~ i64 { return self - v }
            }
            fn main() {
                let i = 1
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
    #[cfg(feature = "generics")]
    fn function_template_using_specs() {
        assert_compiles(
            r#"
            extern fn write(fd: i64, msg: str, len: i64) ~ i64

            spec Task {
                fn run(self) ~ bool
            }
            
            struct PrintTask {
                msg: str
            }
            
            impl PrintTask {
                fn run(self) ~ bool {
                    write(1, self.msg, 100)
                    return true
                }
            }
            
            fn run_task(task: T) ~ bool
            with [T: Task] {
                return task.run()
            }
            
            fn main() {
                let task = PrintTask{msg: "hello world"}
                run_task(task)
            }
        "#,
        )
    }

    #[test]
    #[cfg(feature = "generics")]
    fn templated_methods() {
        assert_compiles(
            r#"
            extern fn exit(code: i64)

            fn assert(b: bool, code: i64) {
                if !b {
                    exit(code)
                }
            }
            
            struct Calculator {
                calc_fn: fn (i64, i64) ~ i64
                accumulator: i64
            }
            
            impl Calculator {
                fn new(f: CalcFn) ~ Calculator
                with [CalcFn = fn (i64, i64) ~ i64] 
                {
                    return Calculator{
                        calc_fn: f
                        accumulator: 0
                    }
                }
            
                fn update(mut self, value: i64) ~ Calculator {
                    let func = self.calc_fn
                    self.accumulator = func(self.accumulator, value)
                    return self
                }
            
                fn with_calc_fn(mut self, f: CalcFn) ~ Calculator 
                with [CalcFn = fn (i64, i64) ~ i64] 
                {
                    self.calc_fn = f
                    return this
                }
            }
            
            fn add(a: i64, b: i64) ~ i64 {
                return a + b
            }
            
            fn mul(a: i64, b: i64) ~ i64 {
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
    #[cfg(feature = "generics")]
    fn nested_tmpl_params() {
        assert_compiles(
            r#"
            fn apply(f: F, arg: T) ~ T
            with [
                T,
                F = fn (T) ~ T,
            ] {
                return f(arg)
            }
            
            fn double(v: i64) ~ i64 {
                return v * 2
            }
            
            fn main() {
                let result: i64 = apply(double, 1)
            }
        "#,
        )
    }

    #[test]
    #[cfg(feature = "generics")]
    fn tmpl_param_type_remap() {
        assert_compiles(
            r#"
            impl i64 {
                fn zero() ~ i64 {
                    return 0
                }
            }
            
            spec Zero {
                fn zero() ~ i64
            }
            
            fn is_zero_value(v: T) ~ bool
            with [T: Zero] {
                return v == T.zero()
            }
            
            fn main() {
                is_zero_value(0)
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
    #[cfg(feature = "generics")]
    fn templated_return_types() {
        assert_compiles(
            r#"
            // Any type that has an associated default member function implments the 
            // Default spec.
            spec Default {
                fn default() ~ T with [T]
            }
            
            // Returns the default value any type that implements the Default spec.
            fn default() ~ T with [T: Default] {
                return T.default()
            }
            
            impl i64 {
                fn default() ~ i64 {
                    return 0
                }
            }
            
            impl u64 {
                fn default() ~ u64 {
                    return 0
                }
            }
            
            struct MyStruct {
                i: i64
                u: u64
            }
            
            impl MyStruct {
                fn default() ~ MyStruct {
                    return MyStruct{
                        i: default()
                        u: default()
                    }
                }
            }
            
            fn main() {
                let my_struct: MyStruct = default()
            }
            "#,
        )
    }

    #[test]
    #[cfg(feature = "generics")]
    fn tmpl_fn_used_as_var() {
        assert_compiles(
            r#"
            fn test(t: T) ~ T 
            with [T] {
                return t
            }
            
            fn apply(f: F, t: T) ~ T
            with [T, F = fn (T) ~ T] {
                return f(t)
            }
            
            fn main() {
                let result: i64 = test(1)
                let t: fn (u64) ~ u64 = test
                let result = apply(t, 234u64)
            }
            "#,
        )
    }

    #[test]
    #[cfg(feature = "generics")]
    fn lambda_as_variable() {
        assert_compiles(
            r#"
            fn max(a: T, b: T) ~ T
            with [T] {
                if a > b {
                    return a
                }
                return b
            }
    
            fn main() {
                let f1: fn (i64, i64) ~ i64 = max
                let f2: fn (u64, u64) ~ u64 = max
                
                let result1 = f1(-3, 4)
                let result2 = f2(12, 642)
            }
            "#,
        )
    }

    #[test]
    #[cfg(feature = "generics")]
    fn lambda_as_argument() {
        assert_compiles(
            r#"
            fn select(selector: F, a: T, b: T) ~ T
            with [T, F = fn (T, T) ~ T] {
                return selector(a, b)
            }
            
            fn main() {
                let result = select($(a, b) b, "not this", "this")
            }
            "#,
        )
    }

    #[test]
    #[cfg(feature = "generics")]
    fn tmpl_fn_with_only_fn_arg() {
        assert_compiles(
            r#"
            fn do(f: fn (T) ~ T) with [T] {}

            fn main() {
                let f: fn (str) ~ str = $(a) a
                do(f)
            }
            "#,
        )
    }

    #[test]
    #[cfg(feature = "generics")]
    fn lambda_with_fn_arg_as_variable() {
        assert_compiles(
            r#"
            fn apply(f: fn (T) ~ T, t: T) ~ T
            with [T] {
                return f(t)
            }
    
            fn main() {
                let a: fn (fn (str) ~ str, str) ~ str = apply
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
                let a = Result::Ok ~== Result::Err
                let r = Result::Err
                
                let b = r ~!= Result::Ok
            }
            "#,
        )
    }
}
