use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func::analyze_fn_sig;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::statement::analyze_statement;
use crate::analyzer::AnalyzeResult;
use crate::parser::program::Program;
use crate::parser::statement::Statement;

fn analyze_program(program: &Program) -> AnalyzeResult<()> {
    let mut ctx = ProgramContext::new();

    // Analyze all function signatures defined at the top level of the program so we can reference
    // them when we analyze statements.
    let mut main_fn = None;
    for statement in &program.statements {
        match statement {
            Statement::FunctionDeclaration(func) => {
                analyze_fn_sig(&mut ctx, &func.signature)?;

                if func.signature.name == "main" {
                    main_fn = Some(&func.signature)
                }
            }
            _ => {}
        }
    }

    // Make sure a main function was declared.
    match main_fn {
        Some(main_sig) => {
            // Make sure main has no args or return.
            if main_sig.args.len() != 0 {
                return Err(AnalyzeError::new(
                    ErrorKind::InvalidMain,
                    "Function main cannot have arguments",
                ));
            }

            if let Some(_) = main_sig.return_type {
                return Err(AnalyzeError::new(
                    ErrorKind::InvalidMain,
                    "Function main cannot have a return type",
                ));
            }
        }
        None => {
            return Err(AnalyzeError::new(
                ErrorKind::MissingMain,
                "Missing main function",
            ));
        }
    }

    // Analyze each statement in the program.
    for statement in &program.statements {
        analyze_statement(&mut ctx, statement)?;
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Cursor};

    use crate::analyzer::error::{AnalyzeError, ErrorKind};
    use crate::analyzer::program::analyze_program;
    use crate::lexer::token::Token;
    use crate::parser::program::Program;

    #[test]
    fn variable_assignment() {
        let raw = r#"
        fn main() {
            int i = 10
            i = 11
        }
        "#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let prog = Program::from(&mut tokens).expect("should not error");
        let result = analyze_program(&prog);
        assert!(matches!(result, Ok(())));
    }

    #[test]
    fn fn_decl() {
        let raw = r#"
        fn main() {}
        fn test(int a, string b) { 
            string s = "hello world!" 
        }"#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let prog = Program::from(&mut tokens).expect("should not error");
        let result = analyze_program(&prog);
        assert!(matches!(result, Ok(())));
    }

    #[test]
    fn fn_already_defined() {
        let raw = r#"
        fn test() {}
        fn test(string thing) {}
        "#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let prog = Program::from(&mut tokens).expect("should not error");
        let result = analyze_program(&prog);
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
        string s = "Hello world!"
        
        fn main() {
            do_thing()
        }
        
        fn do_thing() {
            string v = s
        }
        "#;

        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let prog = Program::from(&mut tokens).expect("should not error");
        let result = analyze_program(&prog);
        assert!(matches!(result, Ok(())));
    }

    #[test]
    fn big_program() {
        let raw = r#"
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
        
        fn print(string s) {}
        
        fn str_concat(string a, string b): string {
            return a
        }
        
        fn itoa(int i): string {
            return "fake"
        }
        "#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let prog = Program::from(&mut tokens).expect("should not error");
        let result = analyze_program(&prog);
        assert_eq!(result, Ok(()));
    }
}
