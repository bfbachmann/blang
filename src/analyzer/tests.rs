#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::analyzer::analyze::{analyze_modules, ProgramAnalysis};
    use crate::analyzer::ast::module::AModule;
    use crate::analyzer::error::{AnalyzeError, AnalyzeResult, ErrorKind};
    use crate::analyzer::warn::{AnalyzeWarning, WarnKind};
    use crate::lexer::lex::lex;
    use crate::lexer::stream::Stream;
    use crate::parser::module::Module;

    fn get_analysis(raw: &str) -> ProgramAnalysis {
        let tokens = lex(raw).expect("should not error");
        let module = Module::from("", &mut Stream::from(tokens)).expect("should not error");
        analyze_modules(vec![module])
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

    fn analyze_program(mods: Vec<(String, String)>) -> ProgramAnalysis {
        let mut parsed_mods = vec![];
        for (mod_path, mod_code) in mods {
            let tokens = lex(mod_code.as_str()).expect("lexing should succeed");
            let parsed_mod = Module::from(mod_path.as_str(), &mut Stream::from(tokens))
                .expect("should not error");
            parsed_mods.push(parsed_mod);
        }

        analyze_modules(parsed_mods)
    }

    fn check_mod_errs(
        program_analysis: &ProgramAnalysis,
        mod_errs: HashMap<String, Vec<ErrorKind>>,
    ) {
        for analyzed_mod in &program_analysis.analyzed_modules {
            let expected_errs = mod_errs.get(analyzed_mod.module.path.as_str()).unwrap();
            let actual_errs = &analyzed_mod.errors;
            assert_eq!(actual_errs.len(), expected_errs.len());
            for err in actual_errs {
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
    fn invalid_main_defs() {
        for code in [
            r#"fn main(a: int) {}"#,
            r#"fn main() -> int { return 0 }"#,
            r#"fn main[T]() {}"#,
        ] {
            let result = analyze(code);
            check_result(result, Some(ErrorKind::InvalidMain));
        }
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
                        fn (n: int) -> bool {
                            print(str_concat("fib visitor sees n=", itoa(n)))
                            return n % 2 == 0
                        },
                    )

                    print(str_concat(prefix, itoa(result)))

                    if i == 10 {
                        break
                    } else if i % 2 == 0 {
                        print("i is even")
                    } else {
                        print("i is odd")
                    }

                    i = i + 1
                }
            }

            // Calls `visitor_fn` with n and returns the n'th Fibonacci number.
            fn fib(n: int, visitor_fn: fn (int) -> bool) -> int {
                if visitor_fn(n) {
                    print("visitor returned true")
                }
                if n <= 1 {
                    return 1
                }
                return fib(n-1, visitor_fn) + fib(n-2, visitor_fn)
            }

            fn print(s: str) {}

            fn str_concat(a: str, b: str) -> str {
                return a
            }

            fn itoa(i: int) -> str {
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

            struct Thing {
                something: bool
                another: Person
            }

            struct Inner {
                count: i64,
                msg: str,
                get_person: fn (str) -> Person,
                thing: Thing,
            }

            struct Outer {
                inner: Inner,
                cond: bool,
            }

            struct Empty {}

            fn get_person(name: str) -> Person {
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
                        thing: Thing {
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

            fn do_thing() -> bool {
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
               func: fn (i64, i64) -> bool,
           }

           fn eq(a: i64, b: i64) -> bool {
               return a == b
           }

           fn neq(a: i64, b: i64) -> bool {
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
                fn get_value(self) -> i64 {
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
    fn generic_fn_with_invalid_spec() {
        let result = analyze(
            r#"
            fn test[T: Thing](t: T) {}
            "#,
        );
        check_result(result, Some(ErrorKind::UndefType));
    }

    #[test]
    fn generic_fn_with_unsatisfied_spec() {
        let result = analyze(
            r#"
            spec Thing {
                fn do_thing()
            }

            struct Doer {}

            fn test[T: Thing](t: T) {}

            fn main() {
                let doer = Doer{}
                test[Doer](doer)
            }
            "#,
        );
        check_result(result, Some(ErrorKind::SpecNotSatisfied));
    }

    #[test]
    fn generic_fn_with_mismatched_shared_generic_types() {
        let result = analyze(
            r#"
            fn do_nothing[T](a: T, b: T) {}

            fn main() {
                do_nothing[int](1, "test")
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn inferred_fn_call_params() {
        let result = analyze(
            r#"
            fn test[A, B](a: A, b: B) {}

            fn main() {
                test(1, 2)
            }
            "#,
        );
        check_result(result, None);
    }

    #[test]
    fn mismatched_inferred_fn_call_params() {
        let result = analyze(
            r#"
            fn test[A](a: A, b: A) {}

            fn main() {
                test(1, "wrong")
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn invalid_inferred_fn_call_params() {
        let result = analyze(
            r#"
            spec Test {
                fn test()
            }

            fn test[T: Test](t: T) {}

            fn main() {
                test(1)
            }
            "#,
        );
        check_result(result, Some(ErrorKind::SpecNotSatisfied));
    }

    #[test]
    fn type_annotations_needed() {
        let result = analyze(
            r#"
            fn test[T]() {}

            fn main() {
                test()
            }
            "#,
        );
        check_result(result, Some(ErrorKind::UnresolvedParams));
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
    fn invalid_generic_extern_fn() {
        let result = analyze(r#"extern fn free[T](rawptr: T)"#);
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
                fn new(inner: i64) -> Value { return Value{inner: inner} }

                fn add(self, v: i64) -> i64 { return self.inner + v }
            }

            struct Thing {
                i: i64
            }

            impl Thing {
                fn new(i: i64) -> Thing {
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
                fn new(inner: i64) -> Value { return Value{inner: inner} }

                fn add(self, v: i64) -> i64 { return self.inner + v }
            }

            struct Thing {
                i: i64
            }

            impl Thing {
                fn new(i: i64) -> Thing {
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
    fn copy_out_of_array() {
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
    fn legal_ptr_deref_with_member_access() {
        let result = analyze(
            r#"
                struct State {i: i64}
    
                fn main() {
                    let state_ptr = &State{i: 0}
                    let i = state_ptr.i
                }
            "#,
        );
        check_result(result, None);
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
    fn invalid_use_of_fn_from_another_scope() {
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
    fn invalid_use_of_type_from_another_scope() {
        let result = analyze(
            r#"
                fn one() {
                    struct Thing {}
                }

                fn two() {
                    let t = Thing {}
                }
            "#,
        );
        check_result(result, Some(ErrorKind::UndefType));
    }

    #[test]
    fn valid_struct_use_in_loop() {
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

                    fn illegal() -> int {
                        return x
                    }
                }
            "#,
        );
        check_result(result, Some(ErrorKind::UndefSymbol));
    }

    #[test]
    fn invalid_use_in_fn() {
        let result = analyze(
            r#"
                fn main() {
                    use "std/libc/mem.bl" @mem
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
        for code in [r#"impl int {}"#, r#"impl str {}"#] {
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


                thing.b &&= false
                thing.b ||= true
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
                    self.value = value
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
                    self.value = value
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
                    } else if false {
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
    fn missing_yield_in_cond() {
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
    fn missing_yield_in_loop() {
        let result = analyze(
            r#"
                fn main() {
                    let result = from loop {
                        if false {
                            yield 1
                        }

                        if true {
                            break
                        }
                    }
                }
            "#,
        );
        check_result(result, Some(ErrorKind::MissingYield));
    }

    #[test]
    fn missing_return_in_loop() {
        let result = analyze(
            r#"
                fn thing() -> int {
                    loop {
                        if false {
                            return 1
                        }

                        if true {
                            break
                        }
                    }
                }
            "#,
        );
        check_result(result, Some(ErrorKind::MissingReturn));
    }

    #[test]
    fn missing_return_in_match() {
        let result = analyze(
            r#"
                fn thing(v: int) -> int {
                    match v {
                    case 0: return 0
                    case let x if x > 0: return 1
                    case:
                    }
                }
            "#,
        );
        check_result(result, Some(ErrorKind::MissingReturn));
    }

    #[test]
    fn missing_return_in_for_loop() {
        let result = analyze(
            r#"
                fn thing() -> int {
                    for let mut i = 0, i < 10, i += 1 {
                        return 1
                    }
                }
            "#,
        );
        check_result(result, Some(ErrorKind::MissingReturn));
    }

    #[test]
    fn yield_outside_from() {
        let result = analyze(
            r#"
                fn thing() {
                    yield 1
                }
            "#,
        );
        check_result(result, Some(ErrorKind::UnexpectedYield));
    }

    #[test]
    fn superfluous_type_cast() {
        let result = analyze(
            r#"
                fn thing() {
                    let x: int = 1 as int
                }
            "#,
        );
        check_result(result, Some(ErrorKind::SuperfluousTypeCast));
    }

    #[test]
    fn cond_ending_with_else_if() {
        let result = analyze(
            r#"
            fn main() {
                if true {} else if false {}
            }
            "#,
        );
        check_result(result, None);
    }

    #[test]
    fn self_referential_type_missing_params() {
        let result = analyze(
            r#"
            struct Thing[T] { ptr: *mut Thing }
            "#,
        );
        check_result(result, Some(ErrorKind::UnresolvedParams));
    }

    #[test]
    fn self_referential_parameterized_type() {
        let result = analyze(
            r#"
            struct Thing[T] {
                ptr: *mut Thing[int]
                value: T
            }

            fn main() {
                let t = Thing[str]{ptr: null, value: "test"}
            }
            "#,
        );
        check_result(result, None);
    }

    #[test]
    fn spec_impl_missing_fns() {
        let result = analyze(
            r#"
            spec Bla {
                fn bla()
            }
            
            struct BlaStruct {}
            impl BlaStruct: Bla {}
            "#,
        );
        check_result(result, Some(ErrorKind::SpecImplMissingFns));
    }

    #[test]
    fn spec_not_defined() {
        let result = analyze(
            r#"
            struct BlaStruct {}
            impl BlaStruct: Bla {}
            "#,
        );
        check_result(result, Some(ErrorKind::UndefType));
    }

    #[test]
    fn ambiguous_access() {
        let result = analyze(
            r#"
            spec A { fn thing() }
            
            struct Thing {}
            impl Thing: A {
                fn thing() {}
            }
            
            spec B { fn thing() }
            impl Thing: B {
                fn thing() {}
            }
            
            fn main() {
                Thing.thing()
            }
            "#,
        );
        check_result(result, Some(ErrorKind::AmbiguousAccess));
    }

    #[test]
    fn spec_member_access() {
        let result = analyze(
            r#"
            spec Bla {
                fn bla()
            }

            fn main() {
                Bla.bla()
            }
            "#,
        );
        check_result(result, Some(ErrorKind::SpecMemberAccess));
    }

    #[test]
    fn non_spec_fn_in_impl() {
        let result = analyze(
            r#"
            spec Bla {
                fn bla()
            }
            
            struct BlaStruct {}
            impl BlaStruct: Bla {
                fn bla() {}
                fn illegal() {}
            }
            "#,
        );
        check_result(result, Some(ErrorKind::NonSpecFnInImpl));
    }

    #[test]
    fn expected_spec() {
        let result = analyze(
            r#"
            struct BlaStruct {}
            impl BlaStruct: int {}
            "#,
        );
        check_result(result, Some(ErrorKind::ExpectedSpec));

        let result = analyze(
            r#"
            struct Other {}
            struct BlaStruct {}
            impl BlaStruct: Other {}
            "#,
        );
        check_result(result, Some(ErrorKind::ExpectedSpec));
    }

    #[test]
    fn incorrect_spec_fn_in_impl() {
        let result = analyze(
            r#"
            spec Bla {
                fn bla()
            }
            
            struct BlaStruct {}
            impl BlaStruct: Bla {
                fn bla(i: int) {}
            }
            "#,
        );
        check_result(result, Some(ErrorKind::IncorrectSpecFnInImpl));
    }

    #[test]
    fn spec_already_implemented() {
        let result = analyze(
            r#"
            spec Bla {
                fn bla()
            }
            
            struct BlaStruct {}
            impl BlaStruct: Bla {
                fn bla() {}
            }
            
            impl BlaStruct: Bla {
                fn bla() {}
            }
            "#,
        );
        check_result(result, Some(ErrorKind::DuplicateSpecImpl));
    }

    #[test]
    fn unexpected_method_params() {
        let result = analyze(
            r#"
            struct Thing {}
            impl Thing {
                fn do_thing() {}
            }

            fn main() {
                Thing.do_thing[int]()
            }
            "#,
        );
        check_result(result, Some(ErrorKind::UnexpectedParams));
    }

    #[test]
    fn unresolved_method_params() {
        let result = analyze(
            r#"
            struct Thing {}
            impl Thing {
                fn do_thing[T]() {}
            }

            fn main() {
                Thing.do_thing()
            }
            "#,
        );
        check_result(result, Some(ErrorKind::UnresolvedParams));
    }

    #[test]
    fn inexhaustive_match() {
        let result = analyze(
            r#"
            enum Thing {
                One
                Two
            }
            
            fn main() {
                match Thing::One {
                case let Thing::One:
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MatchNotExhaustive));
    }

    #[test]
    fn inexhaustive_match_with_if() {
        let result = analyze(
            r#"
            enum Thing {
                One
                Two
            }

            fn main() {
                match Thing::One {
                case let Thing::One:
                case let Thing::Two if false:
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MatchNotExhaustive));
    }

    #[test]
    fn inexhaustive_match_against_int() {
        let result = analyze(
            r#"
            fn main() {
                match 1 {
                case 1:
                case 2:
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MatchNotExhaustive));
    }

    #[test]
    fn inexhaustive_match_against_bool() {
        let result = analyze(
            r#"
            fn main() {
                match true {
                case true:
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MatchNotExhaustive));
    }

    #[test]
    fn exhaustive_match_against_bool() {
        let result = analyze(
            r#"
            fn main() {
                match true {
                case true:
                case false:
                }
            }
            "#,
        );
        check_result(result, None);
    }

    #[test]
    fn unreachable_match_case() {
        let mut analysis = get_analysis(
            r#"
            fn main() {
                match true {
                case true:
                case false:
                case:
                }
            }
            "#,
        )
        .analyzed_modules
        .remove(0);
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
    fn match_case_expr_type_mismatch() {
        let result = analyze(
            r#"
            enum Thing {
                One(int)
            }
            fn main() {
                match Thing::One(1) {
                case 1:
                case:
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn invalid_let_pattern_binding() {
        let result = analyze(
            r#"
            enum Thing {
                One(int)
            }
            fn main() {
                match Thing::One(1) {
                case let invalid():
                case:
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::InvalidPattern));
    }

    #[test]
    fn invalid_binding_expr_in_enum_pattern() {
        let result = analyze(
            r#"
            enum Thing {
                One(int)
            }
            fn main() {
                match Thing::One(1) {
                case let Thing::One(invalid()):
                case:
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::InvalidPattern));
    }

    #[test]
    fn missing_enum_inner_value_binding_in_pattern() {
        let result = analyze(
            r#"
            enum Thing {
                One(int)
            }
            fn main() {
                match Thing::One(1) {
                case let Thing::One:
                case:
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::InvalidPattern));
    }

    #[test]
    fn duplicate_var_pattern_binding() {
        let result = analyze(
            r#"
            enum Thing {
                One(int)
            }
            fn main() {
                match Thing::One(1) {
                case let x, y:
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::ConflictingPattern));
    }

    #[test]
    fn invalid_enum_inner_value_binding_in_empty_variant() {
        let result = analyze(
            r#"
            enum Thing {
                One
            }
            fn main() {
                match Thing::One {
                case let Thing::One(invalid):
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn invalid_enum_case_for_non_enum() {
        let result = analyze(
            r#"
            enum Thing {
                One
            }
            fn main() {
                match "test" {
                case let Thing::One:
                case:
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn wrong_enum_type_in_pattern() {
        let result = analyze(
            r#"
            enum A { One }
            enum B { One }
            fn main() {
                match A::One {
                case let B::One:
                case:
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn unmatchable_type_in_match_case() {
        let result = analyze(
            r#"
            struct Thing {}
            fn main() {
                match Thing{} {
                case Thing{}:
                case:
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn inconsistent_pattern_binding_names() {
        let result = analyze(
            r#"
            enum Thing { One(int), Two(int) }
            fn main() {
                match Thing::One(1) {
                case let Thing::One(x), Thing::Two(y):
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::InconsistentPatternBindingNames));
    }

    #[test]
    fn inconsistent_pattern_binding_types() {
        let result = analyze(
            r#"
            enum Thing { One(int), Two(bool) }
            fn main() {
                match Thing::One(1) {
                case let Thing::One(x), Thing::Two(x):
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::InconsistentPatternBindingTypes));
    }

    #[test]
    fn illegal_pattern_binding() {
        let result = analyze(
            r#"
            enum Thing { One(int), Two(bool) }
            fn main() {
                match Thing::One(1) {
                case let Thing::One(_), Thing::Two(v):
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::IllegalPatternBinding));
    }

    #[test]
    fn inconsistent_pattern_wildcard_binding() {
        let result = analyze(
            r#"
            enum Thing { One(int), Two(bool) }
            fn main() {
                match Thing::One(1) {
                case let Thing::One(v), Thing::Two(_):
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::InconsistentPatternBindingNames));
    }

    #[test]
    fn duplicate_pattern() {
        let result = analyze(
            r#"
            enum Thing { One(int), Two(bool) }
            fn main() {
                match Thing::One(1) {
                case let Thing::One(_), Thing::Two(_), Thing::One(_):
                }
            }
            "#,
        );
        check_result(result, Some(ErrorKind::DuplicatePattern));
    }

    #[test]
    fn private_member_access() {
        let mods = vec![
            (
                "impl.bl".to_string(),
                r#"
                    use "thing.bl" {Thing}
                    fn test() {
                        Thing.do_nothing()
                    }
                "#
                .to_string(),
            ),
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
        ];

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
    fn legal_access_to_pub_spec_fn() {
        let mods = vec![
            // We should be able to use methods on the type that aren't marked pub as long
            // as they're part of the public spec implementation.
            (
                "main.bl".to_string(),
                r#"
                    use "thing.bl" {Thing}
                    fn main() {
                        Thing.bing()
                    }
                "#
                .to_string(),
            ),
            // Declare a type that implements the public spec.
            (
                "thing.bl".to_string(),
                r#"
                    pub spec Bing {
                        fn bing()
                    }
                    pub struct Thing {}
                    impl Thing: Bing {
                        fn bing() {}
                    }
                "#
                .to_string(),
            ),
        ];

        let analysis = analyze_program(mods);
        check_mod_errs(
            &analysis,
            HashMap::from([
                ("main.bl".to_string(), vec![]),
                ("bing.bl".to_string(), vec![]),
                ("thing.bl".to_string(), vec![]),
            ]),
        );
    }

    #[test]
    fn illegal_access_to_priv_spec_fn() {
        let mods = vec![
            // We should not be able to use methods on the type that aren't marked pub because the
            // spec is private.
            (
                "main.bl".to_string(),
                r#"
                    use "bing.bl" {Thing}
                    fn main() {
                        Thing.bing()
                    }
                "#
                .to_string(),
            ),
            // Declare private spec and a type that implements it.
            (
                "bing.bl".to_string(),
                r#"
                    spec Bing {
                        fn bing()
                    }
                    pub struct Thing {}
                    impl Thing: Bing {
                        fn bing() {}
                    }
                "#
                .to_string(),
            ),
        ];

        let analysis = analyze_program(mods);
        check_mod_errs(
            &analysis,
            HashMap::from([
                ("main.bl".to_string(), vec![ErrorKind::UseOfPrivateValue]),
                ("bing.bl".to_string(), vec![]),
            ]),
        )
    }

    #[test]
    fn private_struct_field_init() {
        let mods = vec![
            (
                "impl.bl".to_string(),
                r#"
                    use "thing.bl" {Thing}
                    fn test() {
                        let invalid = Thing{priv_field: 1}
                    }
                "#
                .to_string(),
            ),
            (
                "thing.bl".to_string(),
                r#"
                    pub struct Thing {
                        priv_field: int
                    }
                "#
                .to_string(),
            ),
        ];

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
        let mods = vec![
            (
                "impl.bl".to_string(),
                r#"
                    use "thing.bl" {Thing}
                    fn test() {
                        let illegal = Thing.new().priv_field
                    }
                "#
                .to_string(),
            ),
            (
                "thing.bl".to_string(),
                r#"
                    pub struct Thing {
                        priv_field: int
                    }
        
                    impl Thing {
                        pub fn new() -> Thing {
                            return Thing{priv_field: 0}
                        }
                    }
            "#
                .to_string(),
            ),
        ];

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
    fn private_type_access_via_mod() {
        let mods = vec![
            (
                "impl.bl".to_string(),
                r#"
                    use "thing.bl" @thing
                    fn test() {
                        let t = @thing.Thing{}
                    }
                "#
                .to_string(),
            ),
            ("thing.bl".to_string(), r#"struct Thing {}"#.to_string()),
        ];

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
    fn private_fn_access_via_mod() {
        let mods = vec![
            (
                "impl.bl".to_string(),
                r#"
                    use "thing.bl" @thing
                    fn test() {
                        @thing.test()
                    }
                "#
                .to_string(),
            ),
            ("thing.bl".to_string(), r#"fn test() {}"#.to_string()),
        ];

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
    fn private_const_access_via_mod() {
        let mods = vec![
            (
                "impl.bl".to_string(),
                r#"
                    use "thing.bl" @thing
                    fn test() {
                        let t = @thing.test
                    }
                "#
                .to_string(),
            ),
            ("thing.bl".to_string(), r#"const test = 1"#.to_string()),
        ];

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
