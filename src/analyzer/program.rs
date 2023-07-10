use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::func::analyze_fn_sig;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::statement::RichStatement;
use crate::analyzer::AnalyzeResult;
use crate::parser::program::Program;
use crate::parser::statement::Statement;
use std::os::macos::raw::stat;

#[derive(Debug)]
pub struct RichProg {
    pub statements: Vec<RichStatement>,
}

impl RichProg {
    pub fn from(prog: Program) -> AnalyzeResult<Self> {
        let mut ctx = ProgramContext::new();

        // Analyze all function signatures defined at the top level of the program so we can reference
        // them when we analyze statements.
        let mut main_fn = None;
        for statement in &prog.statements {
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
                        "function main cannot have arguments",
                    ));
                }

                if let Some(_) = main_sig.return_type {
                    return Err(AnalyzeError::new(
                        ErrorKind::InvalidMain,
                        "function main cannot have a return type",
                    ));
                }
            }
            None => {
                return Err(AnalyzeError::new(
                    ErrorKind::MissingMain,
                    "missing main function",
                ));
            }
        }

        // Analyze each statement in the program and collect the results.
        let mut rich_statements = vec![];
        for statement in prog.statements {
            let rich_statement = RichStatement::from(&mut ctx, statement)?;
            rich_statements.push(rich_statement);
        }

        Ok(RichProg {
            statements: rich_statements,
        })
    }
}

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Cursor};

    use crate::analyzer::error::{AnalyzeError, ErrorKind};
    use crate::analyzer::program::RichProg;
    use crate::lexer::token::Token;
    use crate::parser::program::Program;

    #[test]
    fn variable_assignment() {
        let raw = r#"
        fn main() {
            i64 i = 10
            i = 11
        }
        "#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let prog = Program::from(&mut tokens).expect("should not error");
        let result = RichProg::from(prog);
        assert!(matches!(result, Ok(_)));
    }

    #[test]
    fn fn_decl() {
        let raw = r#"
        fn main() {}
        fn test(i64 a, string b) { 
            string s = "hello world!" 
        }"#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let prog = Program::from(&mut tokens).expect("should not error");
        let result = RichProg::from(prog);
        assert!(matches!(result, Ok(_)));
    }

    #[test]
    fn fn_already_defined() {
        let raw = r#"
        fn test() {}
        fn test(string thing) {}
        "#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let prog = Program::from(&mut tokens).expect("should not error");
        let result = RichProg::from(prog);
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
        let result = RichProg::from(prog);
        assert!(matches!(result, Ok(_)));
    }

    #[test]
    fn big_program() {
        let raw = r#"
        fn main() {
            i64 i = 0
            loop {
                string prefix = str_concat(str_concat("Fibonacci number ", itoa(i)), " is: ")
                
                i64 result = fib(
                    i,
                    fn (i64 n): bool {
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
        fn fib(i64 n, fn (i64): bool visitor_fn): i64 {
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
        
        fn itoa(i64 i): string {
            return "fake"
        }
        "#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let prog = Program::from(&mut tokens).expect("should not error");
        let result = RichProg::from(prog);
        assert!(matches!(result, Ok(_)));
    }
}
