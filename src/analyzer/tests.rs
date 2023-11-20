#[cfg(test)]
mod tests {

    use crate::analyzer::analyze::analyze_prog;
    use crate::analyzer::ast::program::AProgram;
    use crate::analyzer::error::{AnalyzeError, AnalyzeResult, ErrorKind};
    use crate::analyzer::prog_context::ProgramAnalysis;
    use crate::analyzer::warn::{AnalyzeWarning, WarnKind};
    use crate::lexer::lex::lex;
    use crate::lexer::stream::Stream;

    use crate::parser::program::Program;

    fn get_analysis(raw: &str) -> ProgramAnalysis {
        let mut char_stream = Stream::from(raw.chars().collect());
        let tokens = lex(&mut char_stream).expect("should not error");
        let prog = Program::from(&mut Stream::from(tokens)).expect("should not error");
        analyze_prog(&prog)
    }

    fn analyze(raw: &str) -> AnalyzeResult<AProgram> {
        let mut analysis = get_analysis(raw);
        if analysis.errors.is_empty() {
            Ok(analysis.prog)
        } else {
            Err(analysis.errors.remove(0))
        }
    }

    fn check_result(result: AnalyzeResult<AProgram>, expected_err_kind: Option<ErrorKind>) {
        match expected_err_kind {
            Some(kind) => assert_eq!(result.unwrap_err().kind, kind),
            None => assert!(result.is_ok()),
        }
    }

    #[test]
    fn call_to_main() {
        let raw = r#"
        fn main() {
            thing()
        }
        
        fn thing() {
            main()
        }
        "#;
        let result = analyze(raw);
        check_result(result, Some(ErrorKind::CallToMain));
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
    fn illegal_nested_fn() {
        let raw = r#"
            fn my_func() {
                fn another() {}
            }
        "#;
        let result = analyze(raw);
        check_result(result, Some(ErrorKind::InvalidStatement));
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
                    fn (n: i64) ~ bool {
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
        fn fib(n: i64, visitor_fn: fn (i64) ~ bool) ~ i64 {
            if visitor_fn(n) {
                print("visitor returned true")
            }
            if n <= 1 {
                return 1
            }
            return fib(n-1, visitor_fn) + fib(n-2, visitor_fn)
        }
        
        fn print(s: str) {}
        
        fn str_concat(a: str, b: str) ~ str {
            return a
        }
        
        fn itoa(i: i64) ~ str {
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
                get_person: fn (str) ~ Person,
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
            
            fn get_person(name: str) ~ Person {
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
            
            fn do_thing() ~ bool {
                return true
                let a = 1
            }
        "#;
        let mut analysis = get_analysis(raw);
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
    fn missing_main() {
        let mut analysis = get_analysis("");
        assert!(analysis.errors.is_empty());
        assert_eq!(analysis.warnings.len(), 1);
        assert!(matches!(
            analysis.warnings.remove(0),
            AnalyzeWarning {
                kind: WarnKind::MissingMain,
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
               func: fn (i64, i64) ~ bool,
           }
           
           fn eq(a: i64, b: i64) ~ bool {
               return a == b
           }
           
           fn neq(a: i64, b: i64) ~ bool {
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
                let b = a.5
            }
            "#,
        );
        check_result(result, Some(ErrorKind::UndefMember));
    }

    #[test]
    fn invalid_tuple_field_assignment() {
        let result = analyze(
            r#"
            fn main() {
                let mut a = {1, 2, 3}
                a.0 = true
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
            const {
                a = {1, 2, true}
                a = "test"
            }
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
                fn get_value(self) ~ i64 {
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
            fn test(a: A, b: B) ~ C with [A, B, C] {
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
                let a = *>1234
            } 
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn invalid_write_dest_pointee_type() {
        let result = analyze(
            r#"
            fn main() {
                let x = *<1
                x <- true
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }

    #[test]
    fn invalid_write_dest_not_ptr() {
        let result = analyze(
            r#"
            fn main() {
                let x = 1
                x <- 1
            }
            "#,
        );
        check_result(result, Some(ErrorKind::MismatchedTypes));
    }
}
