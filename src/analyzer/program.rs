use std::collections::HashMap;

use colored::Colorize;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func_sig::analyze_fn_sig;
use crate::analyzer::func_sig::RichFnSig;
use crate::analyzer::move_check::MoveChecker;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#struct::RichStructType;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::analyzer::statement::RichStatement;
use crate::analyzer::warn::{AnalyzeWarning, WarnKind};
use crate::format_code;
use crate::parser::program::Program;
use crate::parser::statement::Statement;

/// Represents a semantically valid and type-rich program.
#[derive(Debug)]
pub struct RichProg {
    pub statements: Vec<RichStatement>,
}

/// Represents the result of semantic analysis on a program.
pub struct ProgramAnalysis {
    pub prog: RichProg,
    pub types: HashMap<TypeId, RichType>,
    pub errors: Vec<AnalyzeError>,
    pub warnings: Vec<AnalyzeWarning>,
}

impl RichProg {
    /// Performs semantic analysis on the given program and extern functions.
    pub fn analyze(prog: Program) -> ProgramAnalysis {
        let mut ctx = ProgramContext::new();

        // Perform semantic analysis on the program.
        let prog = RichProg::from(&mut ctx, prog);
        let mut errors = ctx.errors();
        let warnings = ctx.warnings();
        let types = ctx.types();

        // Perform move checks and add any errors to our list of errors only if semantic analysis
        // passed.
        if errors.is_empty() {
            errors = MoveChecker::check_prog(&prog, &types);
        }

        ProgramAnalysis {
            prog,
            warnings,
            errors,
            types,
        }
    }

    /// Performs semantic analysis on the given program and returns a type-rich version of it.
    pub fn from(ctx: &mut ProgramContext, prog: Program) -> Self {
        // Analyze top-level struct declarations.
        define_structs(ctx, &prog);

        // Analyze top-level function declarations.
        define_fns(ctx, &prog);

        // Analyze each statement in the program.
        let mut analyzed_statements = vec![];
        for statement in prog.statements {
            match statement {
                Statement::FunctionDeclaration(_)
                | Statement::ExternFns(_)
                | Statement::Consts(_)
                | Statement::StructDeclaration(_)
                | Statement::Impl(_) => {
                    analyzed_statements.push(RichStatement::from(ctx, statement));
                }
                other => {
                    ctx.add_err(AnalyzeError::new(
                        ErrorKind::InvalidStatement,
                        "expected type, constant, or function declaration",
                        &other,
                    ));
                }
            }
        }

        RichProg {
            statements: analyzed_statements,
        }
    }
}

/// Defines top-level struct types in the program context without deeply analyzing their fields, so
/// they can be referenced later. This will simply check for struct type name collisions and
/// containment cycles. We do this before fully analyzing types to prevent infinite recursion.
fn define_structs(ctx: &mut ProgramContext, prog: &Program) {
    // First pass: Define all structs without analyzing their fields. In this pass, we will only
    // check that there are no struct name collisions.
    for statement in &prog.statements {
        match statement {
            Statement::StructDeclaration(struct_type) => {
                if ctx.add_extern_struct(struct_type.clone()).is_some() {
                    ctx.add_err(AnalyzeError::new(
                        ErrorKind::TypeAlreadyDefined,
                        format_code!(
                            "another type with the name {} already exists",
                            struct_type.name
                        )
                        .as_str(),
                        struct_type,
                    ));
                }
            }

            _ => {}
        }
    }

    // Second pass: Check for struct containment cycles.
    let extern_structs = ctx.extern_structs();
    let mut results = vec![];
    for struct_type in extern_structs {
        let result = RichStructType::analyze_containment(ctx, struct_type);
        results.push((result, struct_type.name.clone()));
    }

    // Remove struct types that have containment cycles from the program context and add them as
    // invalid types instead. We do this so we can safely continue with semantic analysis without
    // having to worry about stack overflows during recursive type resolution.
    for (result, struct_type_name) in results {
        if ctx.consume_error(result).is_none() {
            ctx.remove_extern_struct(struct_type_name.as_str());
            ctx.add_invalid_type(struct_type_name.as_str());
        }
    }
}

/// Analyzes all top-level function signatures and defines them in the program context so they
/// can be referenced later. This will not perform any analysis of function bodies.
fn define_fns(ctx: &mut ProgramContext, prog: &Program) {
    let mut main_defined = false;
    for statement in &prog.statements {
        match statement {
            Statement::FunctionDeclaration(func) => {
                analyze_fn_sig(ctx, &func.signature);

                if func.signature.name == "main" {
                    main_defined = true;

                    // Make sure main has no args or return.
                    if func.signature.args.len() != 0 {
                        ctx.add_err(AnalyzeError::new(
                            ErrorKind::InvalidMain,
                            format_code!("function {} cannot have arguments", "main").as_str(),
                            &func.signature,
                        ));
                    }

                    if func.signature.return_type.is_some() {
                        ctx.add_err(AnalyzeError::new(
                            ErrorKind::InvalidMain,
                            format_code!("function {} cannot have a return type", "main").as_str(),
                            &func.signature,
                        ));
                    }
                }
            }

            Statement::ExternFns(ext) => {
                for sig in &ext.fn_sigs {
                    analyze_fn_sig(ctx, sig);
                }
            }

            Statement::Impl(impl_) => {
                // Set the current impl type ID on the program context so we can access it when
                // resolving type `This`.
                let type_id = TypeId::from(impl_.typ.clone());
                ctx.set_impl_type_id(Some(type_id.clone()));

                // Analyze each member function signature and record it as a member of this type
                // in the program context.
                for member_fn in &impl_.member_fns {
                    let fn_sig = RichFnSig::from(ctx, &member_fn.signature);
                    if ctx
                        .get_type_member_fn(&type_id, fn_sig.name.as_str())
                        .is_some()
                    {
                        ctx.add_err(AnalyzeError::new(
                            ErrorKind::FunctionAlreadyDefined,
                            format_code!(
                                "function {} was already defined for type {}",
                                member_fn.signature.name,
                                type_id
                            )
                            .as_str(),
                            &member_fn.signature,
                        ));
                    } else {
                        ctx.add_type_member_fn(type_id.clone(), fn_sig);
                    }
                }

                // Remove the current impl type ID from the program context now that we're done
                // checking the function signatures inside the impl block.
                ctx.set_impl_type_id(None);
            }

            _ => {}
        };
    }

    if !main_defined {
        ctx.add_warn(AnalyzeWarning::new_with_default_pos(
            WarnKind::MissingMain,
            "no main function was detected; your code will not execute",
        ));
    }
}

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Cursor};

    use crate::analyzer::error::AnalyzeResult;
    use crate::analyzer::error::{AnalyzeError, ErrorKind};
    use crate::analyzer::program::{ProgramAnalysis, RichProg};
    use crate::analyzer::warn::{AnalyzeWarning, WarnKind};
    use crate::lexer::token::Token;
    use crate::parser::program::Program;
    use crate::parser::stream::Stream;

    fn get_analysis(raw: &str) -> ProgramAnalysis {
        let tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let prog = Program::from(&mut Stream::from(tokens)).expect("should not error");
        RichProg::analyze(prog)
    }

    fn analyze_prog(raw: &str) -> AnalyzeResult<RichProg> {
        let mut analysis = get_analysis(raw);
        if analysis.errors.is_empty() {
            Ok(analysis.prog)
        } else {
            Err(analysis.errors.remove(0))
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
        let result = analyze_prog(raw);
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::CallToMain,
                ..
            })
        ));
    }

    #[test]
    fn variable_assignment() {
        let raw = r#"
        fn main() {
            let mut i: i64 = 10
            i = 11
        }
        "#;
        let result = analyze_prog(raw);
        assert!(matches!(result, Ok(_)));
    }

    #[test]
    fn immutable_variable_assignment() {
        let raw = r#"
        fn main() {
            let i: i64 = 10
            i = 11
        }
        "#;
        let result = analyze_prog(raw);
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::ImmutableAssignment,
                ..
            })
        ));
    }

    #[test]
    fn mutable_arg() {
        let raw = r#"
            fn my_func(mut arg: i64) {
                arg = 2
            }
        "#;
        let result = analyze_prog(raw);
        assert!(result.is_ok());
    }

    #[test]
    fn illegal_nested_fn() {
        let raw = r#"
            fn my_func() {
                fn another() {}
            }
        "#;
        let result = analyze_prog(raw);
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::InvalidStatement,
                ..
            })
        ));
    }

    #[test]
    fn assign_to_immutable_arg() {
        let raw = r#"
            fn my_func(arg: i64) {
                arg = 2
            }
        "#;
        let result = analyze_prog(raw);
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::ImmutableAssignment,
                ..
            })
        ));
    }

    #[test]
    fn fn_decl() {
        let raw = r#"
        fn main() {}
        fn test(a: i64, b: str) { 
            let s = "hello world!" 
        }"#;
        let result = analyze_prog(raw);
        assert!(matches!(result, Ok(_)));
    }

    #[test]
    fn assign_to_undefined_var() {
        let raw = r#"
        fn main() {
            i = 1
        }
        "#;
        let result = analyze_prog(raw);
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::SymbolNotDefined,
                ..
            })
        ));
    }

    #[test]
    fn fn_already_defined() {
        let raw = r#"
        fn test() {}
        fn test(thing: str) {}
        "#;
        let result = analyze_prog(raw);
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::FunctionAlreadyDefined,
                ..
            })
        ));
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

        let result = analyze_prog(raw);
        assert!(matches!(result, Ok(_)));
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
        let result = analyze_prog(raw);
        assert!(matches!(result, Ok(_)));
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
        let result = analyze_prog(raw);
        assert!(matches!(result, Ok(_)));
    }

    #[test]
    fn direct_struct_containment_cycle() {
        let raw = r#"
            struct Test {
                inner: Test
            }
        "#;
        let result = analyze_prog(raw);
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::InfiniteSizedType,
                ..
            })
        ));
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
        let result = analyze_prog(raw);
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::InfiniteSizedType,
                ..
            })
        ));
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
        let result = analyze_prog(raw);
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::InfiniteSizedType,
                ..
            })
        ));
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
        let result = analyze_prog(
            r#"
            struct A {}
            struct A {}
            "#,
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::TypeAlreadyDefined,
                ..
            })
        ))
    }

    #[test]
    fn struct_member_access() {
        let result = analyze_prog(
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
        assert!(result.is_ok());
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
            let result = analyze_prog(prog);
            assert!(result.is_err());
            assert_eq!(result.err().unwrap().kind, ErrorKind::InvalidStatement);
        }
    }

    #[test]
    fn illegal_move() {
        let result = analyze_prog(
            r#"
            struct T {}
            
            fn main() {
                let t = T{}
                let t1 = t
                let t2 = t 
            }
            "#,
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::UseOfMovedValue,
                ..
            })
        ))
    }

    #[test]
    fn illegal_member_move() {
        let result = analyze_prog(
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
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::UseOfMovedValue,
                ..
            })
        ))
    }

    #[test]
    fn undefined_type_in_struct() {
        let result = analyze_prog(
            r#"
            struct T {
                inner: Inner
            }
            "#,
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::TypeNotDefined,
                ..
            })
        ))
    }

    #[test]
    fn illegal_loop_move() {
        let result = analyze_prog(
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
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::UseOfMovedValue,
                ..
            })
        ))
    }

    #[test]
    fn loop_move() {
        let result = analyze_prog(
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
        assert!(result.is_ok())
    }

    #[test]
    fn nested_loop_move() {
        let result = analyze_prog(
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
        assert!(result.is_ok())
    }

    #[test]
    fn illegal_nested_loop_move() {
        let result = analyze_prog(
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
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::UseOfMovedValue,
                ..
            })
        ))
    }

    #[test]
    fn move_in_branch_with_break() {
        let result = analyze_prog(
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
        assert!(result.is_ok());
    }

    #[test]
    fn illegal_move_in_loop_with_return() {
        let result = analyze_prog(
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
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::UseOfMovedValue,
                ..
            })
        ))
    }

    #[test]
    fn illegal_move_in_branch_with_break() {
        let result = analyze_prog(
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
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::UseOfMovedValue,
                ..
            })
        ))
    }

    #[test]
    fn move_in_branch_with_return() {
        let result = analyze_prog(
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
        assert!(result.is_ok())
    }

    #[test]
    fn partial_moves() {
        let result = analyze_prog(
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
        assert!(result.is_ok())
    }

    #[test]
    fn invalid_operand_types() {
        let result = analyze_prog(
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
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            })
        ))
    }

    #[test]
    fn invalid_tuple_access() {
        let result = analyze_prog(
            r#"
            fn main() {
                let a = {1, 2, 3}
                let b = a.5
            }
            "#,
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::MemberNotDefined,
                ..
            })
        ))
    }

    #[test]
    fn invalid_tuple_field_assignment() {
        let result = analyze_prog(
            r#"
            fn main() {
                let mut a = {1, 2, 3}
                a.0 = true
            }
            "#,
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            })
        ))
    }

    #[test]
    fn illegal_use_of_extern() {
        let result = analyze_prog(
            r#"
            fn main() {
                extern fn nothing()
            }
            "#,
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::InvalidStatement,
                ..
            })
        ))
    }

    #[test]
    fn duplicate_const() {
        let result = analyze_prog(
            r#"
            const {
                a = {1, 2, true}
                a = "test"
            }
            "#,
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::ConstAlreadyDefined,
                ..
            })
        ))
    }

    #[test]
    fn const_type_mismatch() {
        let result = analyze_prog(
            r#"
            const a: {bool, i64, i64} = {1, 2, true}
            "#,
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            })
        ))
    }

    #[test]
    fn illegal_assign_to_const() {
        let result = analyze_prog(
            r#"
            const a = true
            
            fn main() {
                a = false
            }
            "#,
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::ImmutableAssignment,
                ..
            })
        ))
    }

    #[test]
    fn duplicate_member_fn() {
        let result = analyze_prog(
            r#"
            struct T {
                value: i64
            }
            
            impl T {
                fn get_value(this) ~ i64 {
                    return this.value
                }
            }
            
            impl T {
                fn get_value() {}
            }
            "#,
        );
        assert!(matches!(
            result,
            Err(AnalyzeError {
                kind: ErrorKind::FunctionAlreadyDefined,
                ..
            })
        ))
    }
}
