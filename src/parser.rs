use error::ParseError;
use r#type::Type;

pub mod arg;
pub mod branch;
pub mod closure;
pub mod cond;
mod error;
pub mod expr;
pub mod func;
pub mod func_call;
pub mod func_sig;
pub mod r#loop;
pub mod op;
pub mod program;
pub mod statement;
pub mod r#struct;
pub mod r#type;
pub mod var_assign;
pub mod var_dec;

type ParseResult<T> = Result<T, ParseError>;

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Cursor};

    use crate::lexer::kind::TokenKind;
    use crate::lexer::pos::Position;
    use crate::lexer::token::Token;
    use crate::parser::arg::Argument;
    use crate::parser::branch::Branch;
    use crate::parser::closure::Closure;
    use crate::parser::cond::Conditional;
    use crate::parser::error::{ErrorKind, ParseError};
    use crate::parser::expr::Expression;
    use crate::parser::func::Function;
    use crate::parser::func_call::FunctionCall;
    use crate::parser::func_sig::FunctionSignature;
    use crate::parser::op::Operator;
    use crate::parser::program::Program;
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
            let i = 0
        
            loop {
                let prefix = "Fibonacci number " + itoa(i) + " is: "
                let result = fib(
                    i,
                    fn (n: i64): bool {
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
        fn fib(n: i64, visitor_fn: fn (i64): bool): i64 {
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
            Token::tokenize_line("let i: i64 = 123 let j = 1231", 0).expect("should not error");
        let result = Program::from(&mut tokens).expect("should not error");
        assert_eq!(
            result,
            Program {
                statements: vec![
                    Statement::VariableDeclaration(VariableDeclaration::new(
                        Some(Type::I64),
                        "i".to_string(),
                        Expression::I64Literal(123),
                    )),
                    Statement::VariableDeclaration(VariableDeclaration::new(
                        None,
                        "j".to_string(),
                        Expression::I64Literal(1231),
                    ))
                ]
            }
        );
    }

    #[test]
    fn parse_function_declaration() {
        let mut tokens = Token::tokenize_line(
            r#"fn my_fn(arg1: string, arg2: i64): string { let s = "hello world!"; }"#,
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
                        Argument::new("arg2", Type::I64)
                    ],
                    Some(Type::String),
                ),
                Closure::new(
                    vec![Statement::VariableDeclaration(VariableDeclaration::new(
                        None,
                        "s".to_string(),
                        Expression::StringLiteral("hello world!".to_string()),
                    )),],
                    None
                ),
            )
        );

        let mut tokens = Token::tokenize_line(
            "fn bigboi(f: fn (string, i64): bool, i: i64): fn (bool): string {}",
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
                                    Argument::new("", Type::I64)
                                ],
                                Some(Type::Bool),
                            ))),
                        ),
                        Argument::new("i", Type::I64)
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
        let raw = r#"let i = call(,,)"#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let result = Program::from(&mut tokens);
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::ExpectedExprOrCloseParen,
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
        let raw = r#"let i = call())"#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let result = Program::from(&mut tokens);
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::UnmatchedCloseParen,
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
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::UnexpectedEndOfArgs,
                message: _,
                token: None,
            })
        ));
    }

    #[test]
    fn invalid_start_of_expression() {
        let raw = r#"do(&& true)"#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let result = Program::from(&mut tokens);
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::UnexpectedOperator,
                message: _,
                token: Some(Token {
                    kind: TokenKind::LogicalAnd,
                    start: Position { line: 0, col: 3 },
                    end: Position { line: 0, col: 5 },
                }),
            })
        ));
    }

    #[test]
    fn empty_fn_return() {
        let raw = r#"fn my_func(s: string) {
            if s == "dog" {
                return
            }
            
            print("not dog")
        }"#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let result = Program::from(&mut tokens).expect("should not error");
        assert_eq!(
            result,
            Program {
                statements: vec![Statement::FunctionDeclaration(Function::new(
                    FunctionSignature::new("my_func", vec![Argument::new("s", Type::String)], None),
                    Closure::new(
                        vec![
                            Statement::Conditional(Conditional::new(vec![Branch::new(
                                Some(Expression::BinaryOperation(
                                    Box::new(Expression::VariableReference("s".to_string())),
                                    Operator::EqualTo,
                                    Box::new(Expression::StringLiteral("dog".to_string())),
                                )),
                                Closure::new(vec![Statement::Return(None)], None),
                            )])),
                            Statement::FunctionCall(FunctionCall::new(
                                "print",
                                vec![Expression::StringLiteral("not dog".to_string())]
                            ))
                        ],
                        None,
                    )
                ))]
            }
        );
    }

    #[test]
    fn missing_fn_closing_brace() {
        let raw = r#"fn thing(): i64 {
            return 4 / 2 + 8
        "#;
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let result = Program::from(&mut tokens);
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::UnexpectedEndOfStatement,
                message: _,
                token: None,
            })
        ));
    }
}
