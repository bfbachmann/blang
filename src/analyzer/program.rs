use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func::{analyze_fn_sig, RichFnSig};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#struct::RichStruct;
use crate::analyzer::statement::RichStatement;
use crate::analyzer::warn::Warning;

use crate::parser::func_sig::FunctionSignature;
use crate::parser::program::Program;

use crate::parser::statement::Statement;

use colored::Colorize;

/// Represents a semantically valid and type-rich program.
#[derive(Debug)]
pub struct RichProg {
    pub statements: Vec<RichStatement>,
}

/// Represents the result of semantic analysis on a program.
pub struct ProgramAnalysis {
    pub prog: RichProg,
    pub extern_fns: Vec<RichFnSig>,
    pub errors: Vec<AnalyzeError>,
    pub warnings: Vec<Warning>,
}

impl RichProg {
    /// Performs semantic analysis on the given program and extern functions.
    pub fn analyze(prog: Program, extern_fn_sigs: Vec<FunctionSignature>) -> ProgramAnalysis {
        let mut ctx = ProgramContext::new();

        // Analyze external functions to be added to the program.
        let mut rich_extern_fns = vec![];
        for extern_fn_sig in extern_fn_sigs {
            let fn_sig_result = RichFnSig::from(&mut ctx, &extern_fn_sig);
            if let Some(rich_fn_sig) = ctx.consume_error(fn_sig_result) {
                rich_extern_fns.push(rich_fn_sig);
            }
        }

        ProgramAnalysis {
            prog: RichProg::from(&mut ctx, prog),
            extern_fns: rich_extern_fns,
            errors: ctx.errors(),
            warnings: ctx.warnings(),
        }
    }

    /// Performs semantic analysis on the given program and returns a type-rich version of it.
    pub fn from(ctx: &mut ProgramContext, prog: Program) -> Self {
        // Analyze top-level struct declarations.
        define_structs(ctx, &prog);

        // Analyze top-level function declarations.
        define_fns(ctx, &prog);

        // Analyze each statement in the program and collect the results.
        let mut rich_statements = vec![];
        for statement in prog.statements {
            let rich_statement_result = RichStatement::from(ctx, statement);
            if let Some(rich_statement) = ctx.consume_error(rich_statement_result) {
                rich_statements.push(rich_statement);
            }
        }

        RichProg {
            statements: rich_statements,
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
                    ctx.add_err(AnalyzeError::new_with_locatable(
                        ErrorKind::TypeAlreadyDefined,
                        format!(
                            "another type with the name {} already exists",
                            struct_type.name
                        )
                        .as_str(),
                        Box::new(struct_type.clone()),
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
        let result = RichStruct::analyze_containment(ctx, struct_type);
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
    for statement in &prog.statements {
        match statement {
            Statement::FunctionDeclaration(func) => {
                let result = analyze_fn_sig(ctx, &func.signature);
                ctx.consume_error(result);

                if func.signature.name == "main" {
                    // Make sure main has no args or return.
                    if func.signature.args.len() != 0 {
                        ctx.add_err(AnalyzeError::new_with_locatable(
                            ErrorKind::InvalidMain,
                            format!("function `{}` cannot have arguments", "main".blue()).as_str(),
                            Box::new(func.signature.clone()),
                        ));
                    }

                    if func.signature.return_type.is_some() {
                        ctx.add_err(AnalyzeError::new_with_locatable(
                            ErrorKind::InvalidMain,
                            format!("function `{}` cannot have a return type", "main".blue())
                                .as_str(),
                            Box::new(func.signature.clone()),
                        ));
                    }
                }
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Cursor};

    use crate::analyzer::error::AnalyzeResult;
    use crate::analyzer::error::{AnalyzeError, ErrorKind};
    use crate::analyzer::program::RichProg;
    use crate::lexer::token::Token;
    use crate::parser::program::Program;

    fn analyze_prog(raw: &str) -> AnalyzeResult<RichProg> {
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let prog = Program::from(&mut tokens).expect("should not error");
        let mut analysis = RichProg::analyze(prog, vec![]);
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
            let i: i64 = 10
            i = 11
        }
        "#;
        let result = analyze_prog(raw);
        assert!(matches!(result, Ok(_)));
    }

    #[test]
    fn fn_decl() {
        let raw = r#"
        fn main() {}
        fn test(a: i64, b: string) { 
            let s = "hello world!" 
        }"#;
        let result = analyze_prog(raw);
        assert!(matches!(result, Ok(_)));
    }

    #[test]
    fn fn_already_defined() {
        let raw = r#"
        fn test() {}
        fn test(thing: string) {}
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
        let s = "Hello world!"
        
        fn main() {
            do_thing()
        }
        
        fn do_thing() {
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
            let i = 0
            loop {
                let prefix = str_concat(str_concat("Fibonacci number ", itoa(i)), " is: ")
                
                let result = fib(
                    i,
                    fn (n: i64): bool {
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
        fn fib(n: i64, visitor_fn: fn (i64): bool): i64 {
            if visitor_fn(n) {
                print("visitor returned true")
            }
            if n <= 1 {
                return 1
            }
            return fib(n-1, visitor_fn) + fib(n-2, visitor_fn)
        }
        
        fn print(s: string) {}
        
        fn str_concat(a: string, b: string): string {
            return a
        }
        
        fn itoa(i: i64): string {
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
                name: string,
                age: i64,
            }
            
            struct Inner {
                count: i64,
                msg: string,
                get_person: fn (string): Person,
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
            
            fn get_person(name: string): Person {
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
}
