#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::str::FromStr;

    use target_lexicon::Triple;

    use crate::analyzer::analyze::{analyze_modules, ProgramAnalysis};
    use crate::analyzer::ast::module::AModule;
    use crate::analyzer::error::{AnalyzeError, AnalyzeResult, ErrorKind};
    use crate::analyzer::warn::{AnalyzeWarning, WarnKind};
    use crate::codegen::program::init_target;
    use crate::lexer::lex::lex;
    use crate::lexer::stream::Stream;
    use crate::parser::module::Module;

    fn get_analysis(raw: &str) -> ProgramAnalysis {
        let tokens = lex(raw).expect("should not error");
        let module = Module::from("", &mut Stream::from(tokens)).expect("should not error");
        analyze_modules(vec![module], &&new_test_triple())
    }

    fn analyze(raw: &str) -> AnalyzeResult<AModule> {
        let mut analysis = get_analysis(raw).analyzed_modules.remove(0);
        if analysis.errors.is_empty() {
            Ok(analysis.module)
        } else {
            Err(analysis.errors.remove(0))
        }
    }

    fn check_result(result: AnalyzeResult<AModule>, expected_err_kind: Option<ErrorKind>) {
        match expected_err_kind {
            Some(kind) => assert_eq!(result.unwrap_err().kind, kind),
            None => assert!(result.is_ok()),
        }
    }

    fn new_test_triple() -> Triple {
        Triple::from_str(init_target(None).unwrap().as_str().to_str().unwrap()).unwrap()
    }

    fn analyze_program(mods: HashMap<String, String>) -> ProgramAnalysis {
        let mut parsed_mods = vec![];
        for (mod_path, mod_code) in mods {
            let tokens = lex(mod_code.as_str()).expect("lexing should succeed");
            let parsed_mod = Module::from(mod_path.as_str(), &mut Stream::from(tokens))
                .expect("should not error");
            parsed_mods.push(parsed_mod);
        }

        analyze_modules(parsed_mods, &new_test_triple())
    }

    fn check_mod_errs(
        program_analysis: &ProgramAnalysis,
        mod_errs: HashMap<String, Vec<ErrorKind>>,
    ) {
        for analyzed_mod in &program_analysis.analyzed_modules {
            let expected_errs = mod_errs.get(analyzed_mod.module.path.as_str()).unwrap();
            assert_eq!(analyzed_mod.errors.len(), expected_errs.len());
            for err in &analyzed_mod.errors {
                assert!(expected_errs.contains(&err.kind));
            }
        }
    }

    #[test]
    fn variable_assignment() {
        let raw = r#"
        fn main() {
            let mut i: i64 = 10
            i = 11
        }
        "#;
        let result = analyze(raw);
        check_result(result, None);
    }

    #[test]
    fn immutable_variable_assignment() {
        let raw = r#"
        fn main() {
            let i: i64 = 10
            i = 11
        }
        "#;
        let result = analyze(raw);
        check_result(result, Some(ErrorKind::ImmutableAssignment));
    }

    #[test]
    fn mutable_arg() {
        let raw = r#"
            fn my_func(mut arg: i64) {
                arg = 2
            }
        "#;
        let result = analyze(raw);
        check_result(result, None);
    }

    #[test]
    fn assign_to_immutable_arg() {
        let raw = r#"
            fn my_func(arg: i64) {
                arg = 2
            }
        "#;
        let result = analyze(raw);
        check_result(result, Some(ErrorKind::ImmutableAssignment));
    }

    #[test]
    fn fn_decl() {
        let raw = r#"
        fn main() {}
        fn test(a: i64, b: str) {
            let s = "hello world!"
        }"#;
        let result = analyze(raw);
        check_result(result, None);
    }

    #[test]
    fn assign_to_undefined_var() {
        let raw = r#"
        fn main() {
            i = 1
        }
        "#;
        let result = analyze(raw);
        check_result(result, Some(ErrorKind::UndefSymbol));
    }

    #[test]
    fn fn_already_defined() {
        let raw = r#"
        fn test() {}
        fn test(thing: str) {}
        "#;
        let result = analyze(raw);
        check_result(result, Some(ErrorKind::DuplicateFunction));
    }

    #[test]
    fn multiple_functions() {
        let raw = r#"
        fn main() {
            do_thing()
        }

        fn do_thing() {
            let s = "Hello world!"
            let v = s
        }
        "#;

        let result = analyze(raw);
        check_result(result, None);
    }

    #[test]
    fn big_program() {
        let raw = r#"
            fn main() {
                let mut i = 0
                loop {
                    let prefix = str_concat(str_concat("Fibonacci number ", itoa(i)), " is: ")

                    let result = fib(
                        i,
                        fn (n: int): bool {
                            print(str_concat("fib visitor sees n=", itoa(n)))
                            return n % 2 == 0
                        },
                    )

                    print(str_concat(prefix, itoa(result)))

                    if i == 10 {
                        break
                    } elsif i % 2 == 0 {
                        print("i is even")
                    } else {
                        print("i is odd")
                    }

                    i = i + 1
                }
            }

            // Calls `visitor_fn` with n and returns the n'th Fibonacci number.
            fn fib(n: int, visitor_fn: fn (int): bool): int {
                if visitor_fn(n) {
                    print("visitor returned true")
                }
                if n <= 1 {
                    return 1
                }
                return fib(n-1, visitor_fn) + fib(n-2, visitor_fn)
            }

            fn print(s: str) {}

            fn str_concat(a: str, b: str): str {
                return a
            }

            fn itoa(i: int): str {
                return "fake"
            }

            struct MyStruct {
                inner: MyInnerStruct
            }

            struct MyInnerStruct {
                cond: bool
            }

            fn check_struct(s: MyStruct) {}
        "#;
        let result = analyze(raw);
        check_result(result, None);
    }

    #[test]
    fn struct_defs_with_legal_containment() {
        let raw = r#"
            struct Person {
                name: str,
                age: i64,
            }

            struct Inner {
                count: i64,
                msg: str,
                get_person: fn (str): Person,
                inline_struct_field: struct {
                    something: bool,
                    another: Person,
                },
            }

            struct Outer {
                inner: Inner,
                cond: bool,
            }

            struct Empty {}

            fn get_person(name: str): Person {
                return Person{
                    name: "dave",
                    age: 43,
                }
            }

            fn main() {
                let a = Outer{
                    inner: Inner{
                        count: 1,
                        msg: "test",
                        get_person: get_person,
                        inline_struct_field: struct {
                            something: bool,
                            another: Person,
                        } {
                            something: true,
                            another: get_person(""),
                        }
                    },
                    cond: false
                }
            }
        "#;
        let result = analyze(raw);
        check_result(result, None);
    }

    #[test]
    fn direct_struct_containment_cycle() {
        let raw = r#"
            struct Test {
                inner: Test
            }
        "#;
        let result = analyze(raw);
        check_result(result, Some(ErrorKind::InfiniteSizedType));
    }

    #[test]
    fn indirect_struct_containment_cycle() {
        let raw = r#"
            struct Inner {
                count: i64,
                outer: Outer,
            }

            struct Outer {
                cond: bool,
                inner: Inner,
            }
        "#;
        let result = analyze(raw);
        check_result(result, Some(ErrorKind::InfiniteSizedType));
    }

    #[test]
    fn indirect_struct_containment_cycle_via_tuple() {
        let raw = r#"
            struct Inner {
                count: i64,
                outer: {Outer},
            }

            struct Outer {
                cond: bool,
                inner: Inner,
            }
        "#;
        let result = analyze(raw);
        check_result(result, Some(ErrorKind::InfiniteSizedType));
    }

    #[test]
    fn unreachable_code() {
        let raw = r#"
            fn main() {
                do_thing()
            }

            fn do_thing(): bool {
                return true
                let a = 1
            }
        "#;
        let mut analysis = get_analysis(raw).analyzed_modules.remove(0);
        assert!(analysis.errors.is_empty());
        assert_eq!(analysis.warnings.len(), 1);
        assert!(matches!(
            analysis.warnings.remove(0),
            AnalyzeWarning {
                kind: WarnKind::UnreachableCode,
                ..
            }
        ));
    }

    #[test]
    fn type_already_exists() {
        let result = analyze(
            r#"
            struct A {}
            struct A {}
            "#,
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::DuplicateType,
                ..
            })
        ))
    }

    #[test]
    fn struct_member_access() {
        let result = analyze(
            r#"
           struct Thing {
               i: i64,
               func: fn (i64, i64): bool,
           }

           fn eq(a: i64, b: i64): bool {
               return a == b
           }

           fn neq(a: i64, b: i64): bool {
               return !eq(a, b)
           }

           fn main() {
               let mut t = Thing{
                   i: 234,
                   func: eq,
               }

               let is_eq = t.func(t.i, 2)
               t.func = neq
               let is_neq = t.func(t.i, 234)

               let x = t.i
           }
        "#,
        );
        check_result(result, None);
    }

    #[test]
    fn invalid_top_level_statements() {
        let programs = vec![
            r#"let a = 1"#,
            r#"thing = 1"#,
            r#"if true {}"#,
            r#"loop {}"#,
            r#"{}"#,
        ];

        for prog in programs {
            let result = analyze(prog);
            check_result(result, Some(ErrorKind::InvalidStatement));
        }
    }

    #[test]
    fn illegal_move() {
        let result = analyze(
            r#"
            struct T {}

            fn main() {
                let t = T{}
                let t1 = t
                let t2 = t
            }
            "#,
        );
        check_result(result, Some(ErrorKind::UseOfMovedValue));
    }

    #[test]
    fn illegal_member_move() {
        let result = analyze(
            r#"
            struct Inner {}

            struct T {
                inner: Inner
            }

            fn main() {
                let t = T{inner: Inner{}}
                let t1 = t
                let t2 = t.inner
            }
            "#,
        );
        check_result(result, Some(ErrorKind::UseOfMovedValue));
    }

    #[test]
    fn undefined_type_in_struct() {
        let result = analyze(
            r#"
            struct T {
                inner: Inner
            }
            "#,
        );
        check_result(result, Some(ErrorKind::UndefType));
    }

    #[test]
    fn illegal_loop_move() {
        let result = analyze(
            r#"
            struct T {}

            fn main() {
                let t = T{}

                loop {
                    let a = t
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::UseOfMovedValue));
    }

    #[test]
    fn loop_move() {
        let result = analyze(
            r#"
            struct T {}

            fn main() {
                let t = T{}

                loop {
                    let a = t
                    break
                }
            }
            "#,
        );
        check_result(result, None);
    }

    #[test]
    fn nested_loop_move() {
        let result = analyze(
            r#"
            struct T {}

            fn main() {
                let t = T{}

                loop {
                    loop {
                        let a = t
                        break
                    }
                    return
                }
            }
            "#,
        );
        check_result(result, None);
    }

    #[test]
    fn illegal_nested_loop_move() {
        let result = analyze(
            r#"
            struct T {}

            fn main() {
                let t = T{}

                loop {
                    loop {
                        if true {
                            let a = t
                        }
                    }
                    return
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::UseOfMovedValue));
    }

    #[test]
    fn move_in_branch_with_break() {
        let result = analyze(
            r#"
            fn main() {
                struct T {}
                let t = T{}
                loop {
                    if true {
                        let a = t
                        break
                    }

                    let a = t
                    return
                }
            }
            "#,
        );
        check_result(result, None);
    }

    #[test]
    fn illegal_move_in_loop_with_return() {
        let result = analyze(
            r#"
            fn main() {
                struct T {}
                let t = T{}
                loop {
                    if true {
                        let a = t
                        break
                    }

                    let a = t
                    return
                }

                let a = t
            }
            "#,
        );
        check_result(result, Some(ErrorKind::UseOfMovedValue));
    }

    #[test]
    fn illegal_move_in_branch_with_break() {
        let result = analyze(
            r#"
            fn main() {
                struct T {}
                let t = T{}
                loop {
                    if true {
                        let a = t
                        break
                    }
                }

                let b = t
            }
            "#,
        );
        check_result(result, Some(ErrorKind::UseOfMovedValue));
    }

    #[test]
    fn move_in_branch_with_return() {
        let result = analyze(
            r#"
            fn main() {
                struct T {}
                let t = T{}
                loop {
                    if true {
                        let a = t
                        return
                    }
                }

                let b = t
            }
            "#,
        );
        check_result(result, None);
    }

    #[test]
    fn partial_moves() {
        let result = analyze(
            r#"
            struct Inner {}

            struct T {
                inner1: Inner,
                inner2: Inner,
            }

            fn main() {
                let t = T{
                    inner1: Inner{},
                    inner2: Inner{},
                }

                let i1 = t.inner1
                let i2 = t.inner2
            }
            "#,
        );
        check_result(result, None);
    }

    #[test]
    fn invalid_operand_types() {
        let result = analyze(
            r#"
            struct Thing {}
            fn main() {
                let a = Thing{}
                let b = Thing{}

                if a == b {
                    exit(1)
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn invalid_tuple_access() {
        let result = analyze(
            r#"
            fn main() {
                let a = {1, 2, 3}
                let b = a.(5)
            }
            "#,
        );
        check_result(result, Some(ErrorKind::IndexOutOfBounds));
    }

    #[test]
    fn invalid_tuple_field_assignment() {
        let result = analyze(
            r#"
            fn main() {
                let mut a = {1, 2, 3}
                a.(0) = true
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn illegal_use_of_extern() {
        let result = analyze(
            r#"
            fn main() {
                extern fn nothing()
            }
            "#,
        );
        check_result(result, Some(ErrorKind::InvalidStatement));
    }

    #[test]
    fn duplicate_const() {
        let result = analyze(
            r#"
            const a = {1, 2, true}
            const a = "test"
            "#,
        );
        check_result(result, Some(ErrorKind::DuplicateConst));
    }

    #[test]
    fn const_type_mismatch() {
        let result = analyze(
            r#"
            const a: {bool, i64, i64} = {1, 2, true}
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn illegal_assign_to_const() {
        let result = analyze(
            r#"
            const a = true

            fn main() {
                a = false
            }
            "#,
        );
        check_result(result, Some(ErrorKind::ImmutableAssignment));
    }

    #[test]
    fn duplicate_member_fn() {
        let result = analyze(
            r#"
            struct T {
                value: i64
            }

            impl T {
                fn get_value(self): i64 {
                    return self.value
                }
            }

            impl T {
                fn get_value() {}
            }
            "#,
        );
        check_result(result, Some(ErrorKind::DuplicateFunction));
    }

    #[test]
    fn duplicate_enum_variant() {
        let result = analyze(
            r#"
            enum E {
                Thing
                Thing
            }
            "#,
        );
        check_result(result, Some(ErrorKind::DuplicateEnumVariant));
    }

    #[test]
    fn type_already_defined() {
        let result = analyze(
            r#"
            enum E {}
            struct E {}
            "#,
        );
        check_result(result, Some(ErrorKind::DuplicateType));

        let result = analyze(r#"enum i64 {}"#);
        check_result(result, Some(ErrorKind::DuplicateType));
    }

    #[test]
    fn illegal_direct_enum_containment_cycle() {
        let result = analyze(
            r#"
            enum E {
                Thing(T)
            }

            struct T {
                e: E
            }
            "#,
        );
        check_result(result, Some(ErrorKind::InfiniteSizedType));
    }

    #[test]
    fn illegal_indirect_enum_containment_cycle() {
        let result = analyze(
            r#"
            enum E {
                Thing(E)
            }
            "#,
        );
        check_result(result, Some(ErrorKind::InfiniteSizedType));
    }

    #[test]
    fn duplicate_spec() {
        let result = analyze(
            r#"
            spec A {}
            spec A {}
            "#,
        );
        check_result(result, Some(ErrorKind::DuplicateSpec));
    }

    #[test]
    fn duplicate_fn_arg() {
        let result = analyze(
            r#"
            fn test(a: i64, a: bool) {}
            "#,
        );
        check_result(result, Some(ErrorKind::DuplicateFnArg));
    }

    #[test]
    #[cfg(feature = "generics")]
    fn function_template_with_invalid_spec() {
        let result = analyze(
            r#"
            fn test(t: T)
            with [T: Thing]
            {}
            "#,
        );
        check_result(result, Some(ErrorKind::UndefSpec));
    }

    #[test]
    #[cfg(feature = "generics")]
    fn function_template_with_unsatisfied_spec() {
        let result = analyze(
            r#"
            spec Thing {
                fn do_thing()
            }

            struct Doer {}

            fn test(t: T)
            with [T: Thing]
            {}

            fn main() {
                let doer = Doer{}
                test(doer)
            }
            "#,
        );
        check_result(result, Some(ErrorKind::SpecNotSatisfied));
    }

    #[test]
    #[cfg(feature = "generics")]
    fn function_template_with_unmatched_required_type() {
        let result = analyze(
            r#"
            struct Doer {}

            fn test(t: T)
            with [T = Doer]
            {}

            fn main() {
                let doer = 1
                test(doer)
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    #[cfg(feature = "generics")]
    fn function_template_with_mismatched_shared_templated_types() {
        let result = analyze(
            r#"
            fn do_nothing(a: T, b: T) with [T] {}

            fn main() {
                do_nothing(1, "test")
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    #[cfg(feature = "generics")]
    fn unresolved_tmpl_params() {
        let result = analyze(
            r#"
            fn test(a: A, b: B): C with [A, B, C] {
                return a + b
            }

            fn main() {
                test(1, 2)
            }
            "#,
        );
        check_result(result, Some(ErrorKind::UnresolvedTmplParams));
    }

    #[test]
    fn incompatible_type_cast() {
        let result = analyze(
            r#"
            fn main() {
                let a = 5u64
                let b = a as bool
            }
            "#,
        );
        check_result(result, Some(ErrorKind::InvalidTypeCast));
    }

    #[test]
    fn invalid_expression_is_type() {
        let result = analyze(
            r#"
            fn main() {
                let a = u64
            }
            "#,
        );
        check_result(result, Some(ErrorKind::ExpectedExpr));
    }

    #[test]
    #[cfg(feature = "generics")]
    fn invalid_tmpl_extern_fn() {
        let result = analyze(r#"extern fn free(rawptr: T) with [T]"#);
        check_result(result, Some(ErrorKind::InvalidExtern));
    }

    #[test]
    fn binary_expr_type_coercion() {
        let result = analyze(
            r#"
            fn main() {
                let a = 8u64 - 14 % 2 == 0
            }
        "#,
        );
        check_result(result, None);

        let result = analyze(
            r#"
            fn main() {
                let a: u64 = 8 - 5i64
            }
        "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn redefined_moved_value() {
        let result = analyze(
            r#"
            struct S {}

            fn main() {
                let a = S{}
                let aa = a
                let aa = aa
                let aa = aa
            }
            "#,
        );
        check_result(result, None);
    }

    #[test]
    fn invalid_deref() {
        let result = analyze(
            r#"
            fn main() {
                let a = 1234^
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn non_const_array_len() {
        let result = analyze(
            r#"
            fn main() {
                let len: uint = 2
                let x = [1; len]
            }
            "#,
        );
        check_result(result, Some(ErrorKind::InvalidArraySize));
    }

    #[test]
    fn non_const_array_type_len() {
        let result = analyze(
            r#"
            fn main() {
                let len: uint = 2
                let x: [bool; len] = [true, false]
            }
            "#,
        );
        check_result(result, Some(ErrorKind::InvalidArraySize));
    }

    #[test]
    fn array_elem_type_mismatch() {
        let result = analyze(
            r#"
            fn main() {
                let x: [bool; 2] = [true, "test"]
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn call_chain() {
        let result = analyze(
            r#"
            struct Value {
                inner: i64
            }

            impl Value {
                fn new(inner: i64): Value { return Value{inner: inner} }

                fn add(self, v: i64): i64 { return self.inner + v }
            }

            struct Thing {
                i: i64
            }

            impl Thing {
                fn new(i: i64): Thing {
                    return Thing{
                        i: i
                    }
                }
            }

            fn main() {
                let t = Value.new(Thing.new(74).i).add(2)
            }
            "#,
        );
        check_result(result, None);
    }

    #[test]
    fn invalid_call_chain() {
        let result = analyze(
            r#"
            struct Value {
                inner: i64
            }

            impl Value {
                fn new(inner: i64): Value { return Value{inner: inner} }

                fn add(self, v: i64): i64 { return self.inner + v }
            }

            struct Thing {
                i: i64
            }

            impl Thing {
                fn new(i: i64): Thing {
                    return Thing{
                        i: i
                    }
                }
            }

            fn main() {
                let t = Thing.new(74).i.add(2)
            }
            "#,
        );
        check_result(result, Some(ErrorKind::UndefMember));
    }

    #[test]
    fn array_index_out_of_bounds() {
        let result = analyze(r#"const oob = [1, 2, 3].(5)"#);
        check_result(result, Some(ErrorKind::IndexOutOfBounds));
    }

    #[test]
    fn array_index_wrong_type() {
        let result = analyze(
            r#"
            fn main() {
                let wrong_type = [1, 2, 3].(true)
            }"#,
        );

        check_result(result, Some(ErrorKind::MismatchedTypes));

        let result = analyze(
            r#"
            fn main() {
                let wrong_type = [1, 2, 3].(-2)
            }"#,
        );

        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn use_of_moved_array() {
        let result = analyze(
            r#"
            fn main() {
                let array = [true]
                let moved = array
                let illegal = array.(0)
            }
        "#,
        );
        check_result(result, Some(ErrorKind::UseOfMovedValue));
    }

    #[test]
    fn legal_move_out_of_array() {
        let result = analyze(
            r#"
                fn main() {
                    let array = [[true]]
                    let legal = array.(0)
                }
            "#,
        );
        check_result(result, None);
    }

    #[test]
    fn illegal_move_out_of_array() {
        let result = analyze(
            r#"
                fn main() {
                    let array = [[true]]
                    let legal = array.(0)
                    let illegal = array.(0)
                }
            "#,
        );
        check_result(result, Some(ErrorKind::UseOfMovedValue));
    }

    #[test]
    fn illegal_move_in_array_index() {
        let result = analyze(
            r#"
            fn take(array: [int; 2]): uint {
                return 1
            }

            fn main() {
                let array = [1, 2]
                let illegal = array.(take(array))
            }
        "#,
        );
        check_result(result, Some(ErrorKind::UseOfMovedValue));
    }

    #[test]
    fn illegal_move_in_enum_init() {
        let result = analyze(
            r#"
            struct Thing {}

            enum Test {
                One(Thing)
                Two
            }

            fn main() {
                let thing = Thing{}
                let moved = thing
                let test = Test::One(thing)
            }
        "#,
        );
        check_result(result, Some(ErrorKind::UseOfMovedValue));
    }

    #[test]
    fn illegal_move_in_struct_init() {
        let result = analyze(
            r#"
            struct Thing {}

            struct Test {
                thing: Thing
            }

            fn main() {
                let thing = Thing{}
                let moved = thing
                let test = Test{thing: thing}
            }
        "#,
        );
        check_result(result, Some(ErrorKind::UseOfMovedValue));
    }

    #[test]
    fn illegal_move_in_tuple_init() {
        let result = analyze(
            r#"
            struct Thing {}

            fn main() {
                let thing = Thing{}
                let moved = thing
                let test = {thing}
            }
        "#,
        );
        check_result(result, Some(ErrorKind::UseOfMovedValue));
    }

    #[test]
    fn illegal_assign_to_array_literal() {
        let result = analyze(
            r#"
            fn main() {
                [1, 2].(0) = 0
            }
        "#,
        );
        check_result(result, Some(ErrorKind::InvalidAssignmentTarget));
    }

    #[test]
    fn invalid_mut_ref() {
        let result = analyze(
            r#"
            fn main() {
                let a = true
                let b = &mut a
            }
        "#,
        );
        check_result(result, Some(ErrorKind::InvalidMutRef));
    }

    #[test]
    fn invalid_assign_to_ref() {
        let result = analyze(
            r#"
            fn main() {
                let a = &true
                a^ = false
            }
        "#,
        );
        check_result(result, Some(ErrorKind::ImmutableAssignment));
    }

    #[test]
    fn mut_ref_type_mismatch() {
        let result = analyze(
            r#"
            fn main() {
                let a: *mut i64 = &0
            }
        "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn immutable_ref_type_coercion() {
        let result = analyze(
            r#"
            fn main() {
                // This is valid because `*mut _` coerces to `*_`.
                let a: *int = &mut 0
            }
        "#,
        );
        check_result(result, None);
    }

    #[test]
    fn invalid_pointer_cast() {
        let result = analyze(
            r#"
            fn main() {
                let a = true
                let a_ptr = &a as *mut i64
            }
        "#,
        );
        check_result(result, Some(ErrorKind::InvalidTypeCast));
    }

    #[test]
    fn invalid_negation() {
        let result = analyze(
            r#"
            fn main() {
                let a = -true
            }
        "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn illegal_move_by_deref() {
        let result = analyze(
            r#"
            struct State {}

            fn main() {
                let new = (&State{})^
            }
        "#,
        );
        check_result(result, Some(ErrorKind::IllegalMove));
    }

    #[test]
    fn legal_ptr_deref_with_member_access() {
        let result = analyze(
            r#"
                struct State {i: i64}
    
                fn main() {
                    let state_ptr = &State{i: 0}
                    let i = state_ptr^.i
                }
            "#,
        );
        check_result(result, None);
    }

    #[test]
    fn illegal_ptr_deref_with_member_access() {
        let result = analyze(
            r#"
            struct State {i: {}}

            fn main() {
                let state_ptr = &State{i: {}}
                let i = state_ptr^.i
            }
        "#,
        );
        check_result(result, Some(ErrorKind::IllegalMove));
    }

    #[test]
    fn out_of_order_const_decls() {
        let result = analyze(
            r#"
            const X = Y + 2
            const Y = Z * W
            const W = Z - 1
            const Z = 4
        "#,
        );
        check_result(result, None);
    }

    #[test]
    fn array_indexing_in_loop() {
        let result = analyze(
            r#"
            fn main() {
                let array = [0; 10]
                loop {
                    let x = array.(0)
                }
            }
        "#,
        );
        check_result(result, None);
    }

    #[test]
    fn cast_int_to_ptr() {
        let result = analyze(
            r#"
            fn main() {
                let a = ((&2) as u64) as *str
            }
        "#,
        );
        check_result(result, None);
    }

    #[test]
    fn int_coercion() {
        let result = analyze(
            r#"
            const x: i8 = 123
        "#,
        );
        check_result(result, None);
    }

    #[test]
    fn mut_ref_undefined_symbol() {
        let result = analyze(
            r#"
                fn main() {
                    let x = &mut f
                }
            "#,
        );
        check_result(result, Some(ErrorKind::UndefSymbol));
    }

    #[test]
    fn invalid_nested_fn_use() {
        let result = analyze(
            r#"
                fn one() {
                    fn inner() {}
                }

                fn two() {
                    inner()
                }
            "#,
        );
        check_result(result, Some(ErrorKind::UndefSymbol));
    }

    #[test]
    fn valid_struck_use_in_loop() {
        let result = analyze(
            r#"
                struct S { arr: [int; 1] }
                fn main() {
                    let s = S{arr: [3]}
                    loop {
                        let v = s.arr.(0)
                    }
                }
            "#,
        );
        check_result(result, None);
    }

    #[test]
    fn duplicate_nested_fn() {
        let result = analyze(
            r#"
                fn main() {
                    fn f() {}
                    fn f() {}
                }
            "#,
        );
        check_result(result, Some(ErrorKind::DuplicateFunction));
    }

    #[test]
    fn illegal_use_of_value_from_parent_fn() {
        let result = analyze(
            r#"
                fn main() {
                    let x = 1

                    fn illegal(): int {
                        return x
                    }
                }
            "#,
        );
        check_result(result, Some(ErrorKind::UndefSymbol));
    }

    #[test]
    fn legal_repeated_move_in_array_init() {
        let result = analyze(
            r#"
                struct Test {}
                fn main() {
                    let a = [Test{}; 2]
                }
            "#,
        );
        check_result(result, None);
    }

    #[test]
    fn legal_move_before_reassign_in_array_init() {
        let result = analyze(
            r#"
                struct Test {
                    inner: {}
                }

                fn main() {
                    let mut t = Test{inner: {}}
                    loop {
                        take(t.inner)
                        t.inner = {}
                    }
                }

                fn take(inner: {}) {}
            "#,
        );
        check_result(result, None);
    }

    #[test]
    fn illegal_repeated_move_in_array_init() {
        let result = analyze(
            r#"
                struct Test {}
                fn main() {
                    let t = Test{}
                    let a = [t; 2]
                }
            "#,
        );
        check_result(result, Some(ErrorKind::UseOfMovedValue));
    }

    #[test]
    fn invalid_use_in_fn() {
        let result = analyze(
            r#"
                fn main() {
                    use mem: "std/libc/mem.bl"
                }
            "#,
        );
        check_result(result, Some(ErrorKind::InvalidStatement));
    }

    #[test]
    fn invalid_ptr_index_type() {
        let result = analyze(
            r#"
                fn main() {
                    let x = 1
                    let ptr = &x
                    let index: uint = 123
                    let ptr_at_offset = ptr.(index)
                }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn no_int_type_coercion_with_explicit_type() {
        let result = analyze(
            r#"
                fn main() {
                    let x: uint = 1int
                }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn no_f64_type_coercion_with_explicit_type() {
        let result = analyze(
            r#"
                fn main() {
                    let x: f32 = 1.0f64
                }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn integer_literals_out_of_range() {
        for lit in ["i8", "u8", "i32", "u32"] {
            let result = analyze(
                format!(
                    "fn main() {{
                    let x: {} = 99999999999999999
                }}",
                    lit
                )
                .as_str(),
            );
            check_result(result, Some(ErrorKind::LiteralOutOfRange));
        }
    }

    #[test]
    fn float_literals_out_of_range() {
        let result = analyze(
            r#"
            fn main() {
                let x: f32 = 9.9e99999999999999999999999999999999
            }
            "#,
        );
        check_result(result, Some(ErrorKind::LiteralOutOfRange));
    }

    #[test]
    fn undef_mod_name_in_symbol() {
        let result = analyze(
            r#"
            fn main() {
                let x = @thing.value
            }
            "#,
        );
        check_result(result, Some(ErrorKind::UndefMod));
    }

    #[test]
    fn undef_mod_name_in_type() {
        let result = analyze(
            r#"
            fn main() {
                let x = @thing.Thing{}
            }
            "#,
        );
        check_result(result, Some(ErrorKind::UndefMod));
    }

    #[test]
    fn illegal_impls() {
        for code in [
            r#"impl int {}"#,
            r#"impl str {}"#,
            r#"impl {} {}"#,
            r#"impl {bool, int} {}"#,
            r#"impl [] {}"#,
            r#"impl [int; 3] {}"#,
            r#"impl *u8 {}"#,
        ] {
            let result = analyze(code);
            check_result(result, Some(ErrorKind::IllegalImpl));
        }
    }

    #[test]
    fn invalid_use_of_member_fn() {
        let result = analyze(
            r#"
            struct Thing {}
            impl Thing {
                fn bing() {}
            }
            
            fn test() {
                // This is illegal becauase `bing` is not a method.
                Thing{}.bing()
            }
        "#,
        );
        check_result(result, Some(ErrorKind::UndefMember));
    }

    #[test]
    fn inc_assign_to_field() {
        let result = analyze(
            r#"
            struct Thing {
                value: int
                b: bool
            }
            fn test() {
                let mut thing = Thing{value: 1, b: false}
                thing.value += 1
                thing.value -= 3
                thing.value *= 9
                thing.value /= 6
                thing.value %= 2


                thing.b and= false
                thing.b or= true
            }
        "#,
        );
        check_result(result, None);
    }

    #[test]
    fn illegal_implicit_ref_on_method_call() {
        let result = analyze(
            r#"
            struct Thing {
                value: int
            }
            
            impl Thing {
                fn set_value(*mut self, value: int) {
                    self^.value = value
                }
            }
            
            fn main() {
                let thing = Thing{value: 1}
                thing.set_value(2)
            }
        "#,
        );
        check_result(result, Some(ErrorKind::InvalidMutRef));
    }

    #[test]
    fn illegal_method_call_via_immutable_ref() {
        let result = analyze(
            r#"
            struct Thing {
                value: int
            }

            impl Thing {
                fn set_value(*mut self, value: int) {
                    self^.value = value
                }
            }

            fn main() {
                let thing = &Thing{value: 1}
                thing.set_value(2)
            }
        "#,
        );
        check_result(result, Some(ErrorKind::InvalidMutRef));
    }

    #[test]
    fn illegal_assign_to_intrinsic() {
        let result = analyze(
            r#"
            fn main() {
                null = 2
            }
        "#,
        );
        check_result(result, Some(ErrorKind::InvalidAssignmentTarget));
    }

    #[test]
    fn inconsistent_yield_type() {
        let result = analyze(
            r#"
                fn main() {
                    let result = from if true {
                        yield 1
                    } elsif false {
                        yield "bing"
                    } else {
                        yield 3
                    }
                }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn wrong_yield_type() {
        let result = analyze(
            r#"
                fn main() {
                    let result: bool = from if true {
                        yield 1
                    } else {
                        yield 3
                    }
                }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn missing_yield() {
        let result = analyze(
            r#"
                fn main() {
                    let result = from {
                        if false {
                            yield 1
                        }
    
                        return
                    }
    
                }
            "#,
        );
        check_result(result, Some(ErrorKind::MissingYield));
    }

    #[test]
    fn private_member_access() {
        let mods = HashMap::from([
            (
                "thing.bl".to_string(),
                r#"
                    pub struct Thing {}
                    impl Thing {
                        fn do_nothing() {}
                    }
                "#
                .to_string(),
            ),
            (
                "impl.bl".to_string(),
                r#"
                    use {Thing}: "thing.bl"
                    fn test() {
                        Thing.do_nothing()
                    }
                "#
                .to_string(),
            ),
        ]);

        let analysis = analyze_program(mods);
        check_mod_errs(
            &analysis,
            HashMap::from([
                ("impl.bl".to_string(), vec![ErrorKind::UseOfPrivateValue]),
                ("thing.bl".to_string(), vec![]),
            ]),
        );
    }

    #[test]
    fn private_struct_field_init() {
        let mods = HashMap::from([
            (
                "thing.bl".to_string(),
                r#"
                    pub struct Thing {
                        priv_field: int
                    }
                "#
                .to_string(),
            ),
            (
                "impl.bl".to_string(),
                r#"
                    use {Thing}: "thing.bl"
                    fn test() {
                        let invalid = Thing{priv_field: 1}
                    }
                "#
                .to_string(),
            ),
        ]);

        let analysis = analyze_program(mods);
        check_mod_errs(
            &analysis,
            HashMap::from([
                ("impl.bl".to_string(), vec![ErrorKind::UseOfPrivateValue]),
                ("thing.bl".to_string(), vec![]),
            ]),
        );
    }

    #[test]
    fn private_struct_field_access() {
        let mods = HashMap::from([
            (
                "thing.bl".to_string(),
                r#"
                    pub struct Thing {
                        priv_field: int
                    }
        
                    impl Thing {
                        fn new(): Thing {
                            return Thing{priv_field: 0}
                        }
                    }
            "#
                .to_string(),
            ),
            (
                "impl.bl".to_string(),
                r#"
                    use {Thing}: "thing.bl"
                    fn test() {
                        let illegal = Thing.new().priv_field
                    }
                "#
                .to_string(),
            ),
        ]);

        let analysis = analyze_program(mods);
        check_mod_errs(
            &analysis,
            HashMap::from([
                ("impl.bl".to_string(), vec![ErrorKind::UseOfPrivateValue]),
                ("thing.bl".to_string(), vec![]),
            ]),
        );
    }
}
