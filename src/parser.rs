use error::ParseError;
use r#type::Type;

mod arg;
mod branch;
mod closure;
mod cond;
mod error;
mod expr;
mod r#fn;
mod fn_call;
mod func_sig;
mod r#loop;
mod op;
pub mod program;
pub mod statement;
mod r#type;
mod var_assign;
mod var_dec;

type ParseResult<T> = Result<T, ParseError>;

#[cfg(test)]
mod tests {
    use crate::lexer::kind::TokenKind;
    use crate::lexer::pos::Position;
    use std::io::{BufRead, Cursor};

    use crate::lexer::token::Token;
    use crate::parser::arg::Argument;
    use crate::parser::closure::Closure;
    use crate::parser::error::ParseError;
    use crate::parser::expr::Expression;
    use crate::parser::fn_call::FunctionCall;
    use crate::parser::func_sig::FunctionSignature;
    use crate::parser::program::Program;
    use crate::parser::r#fn::Function;
    use crate::parser::r#type::Type;
    use crate::parser::statement::Statement;
    use crate::parser::var_dec::VariableDeclaration;

    #[test]
    fn parse_identifier() {
        let mut tokens = Token::tokenize_line("something", 0).expect("should not error");
        let result = Program::parse_identifier(&mut tokens).expect("should not error");
        assert_eq!(result, "something");
    }

    #[test]
    fn parse_program() {
        let raw_code = r#"
        fn main() {
            int i = 0
        
            loop {
                string prefix = "Fibonacci number " + itoa(i) + " is: "
                int result = fib(
                    i,
                    fn (int n): bool {
                        print("fib visitor sees n=" + itoa(n))
                        return n % 2 == 0
                    },
                )
        
                print(prefix + itoa(result))
        
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
        
            return fib(n-1) + fib(n-2)
        }
        
        fn do_nothing() {
            return
        }
        "#;
        let mut tokens = Token::tokenize(Cursor::new(raw_code).lines()).expect("should not error");
        Program::from(&mut tokens).expect("should not error");

        let mut tokens =
            Token::tokenize_line("int i = 123 int j = 1231", 0).expect("should not error");
        let result = Program::from(&mut tokens).expect("should not error");
        assert_eq!(
            result,
            Program {
                statements: vec![
                    Statement::VariableDeclaration(VariableDeclaration::new(
                        Type::Int,
                        "i".to_string(),
                        Expression::IntLiteral(123),
                    )),
                    Statement::VariableDeclaration(VariableDeclaration::new(
                        Type::Int,
                        "j".to_string(),
                        Expression::IntLiteral(1231),
                    ))
                ]
            }
        );
    }

    #[test]
    fn parse_function_declaration() {
        let mut tokens = Token::tokenize_line(
            r#"fn my_fn(string arg1, int arg2): string { string s = "hello world!"; }"#,
            0,
        )
        .expect("should not error");
        let result = Function::from(&mut tokens).expect("should not error");
        assert_eq!(
            result,
            Function::new(
                FunctionSignature::new(
                    "my_fn",
                    vec![
                        Argument::new("arg1", Type::String),
                        Argument::new("arg2", Type::Int)
                    ],
                    Some(Type::String),
                ),
                Closure::new(
                    vec![Statement::VariableDeclaration(VariableDeclaration::new(
                        Type::String,
                        "s".to_string(),
                        Expression::StringLiteral("hello world!".to_string()),
                    )),],
                    None
                ),
            )
        );

        let mut tokens = Token::tokenize_line(
            "fn bigboi(fn (string, int): bool f, int i): fn (bool): string {}",
            0,
        )
        .expect("should not error");
        let result = Function::from(&mut tokens).expect("should not error");
        assert_eq!(
            result,
            Function::new(
                FunctionSignature::new(
                    "bigboi",
                    vec![
                        Argument::new(
                            "f",
                            Type::Function(Box::new(FunctionSignature::new_anon(
                                vec![
                                    Argument::new("", Type::String),
                                    Argument::new("", Type::Int)
                                ],
                                Some(Type::Bool),
                            ))),
                        ),
                        Argument::new("i", Type::Int)
                    ],
                    Some(Type::Function(Box::new(FunctionSignature::new_anon(
                        vec![Argument::new("", Type::Bool)],
                        Some(Type::String),
                    )))),
                ),
                Closure::new(vec![], None),
            )
        );
    }

    #[test]
    fn parse_function_call() {
        let mut tokens =
            Token::tokenize_line(r#"do_thing("one", "two", true)"#, 0).expect("should not error");
        let result = FunctionCall::from(&mut tokens).expect("should not error");
        assert_eq!(
            result,
            FunctionCall::new(
                "do_thing",
                vec![
                    Expression::StringLiteral("one".to_string()),
                    Expression::StringLiteral("two".to_string()),
                    Expression::BoolLiteral(true),
                ]
            )
        );
    }

    #[test]
    fn invalid_extra_comma() {
        let raw = r#"int i = call(,,)"#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let result = Program::from(&mut tokens);
        assert!(matches!(
            result,
            Err(ParseError {
                message: _,
                token: Some(Token {
                    kind: TokenKind::Comma,
                    start: Position { line: 0, col: 13 },
                    end: Position { line: 0, col: 14 },
                }),
            })
        ));
    }

    #[test]
    fn invalid_extra_close_paren() {
        let raw = r#"int i = call())"#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let result = Program::from(&mut tokens);
        assert!(matches!(
            result,
            Err(ParseError {
                message: _,
                token: Some(Token {
                    kind: TokenKind::RightParen,
                    start: Position { line: 0, col: 14 },
                    end: Position { line: 0, col: 15 },
                }),
            })
        ));
    }

    #[test]
    fn invalid_missing_close_paren() {
        let raw = r#"do(((x+3) > 2) || other"#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let result = Program::from(&mut tokens);
        dbg!(&result);
        let msg = "Unexpected end of arguments".to_string();
        assert!(matches!(result, Err(ParseError { message: msg, .. })));
    }
}
