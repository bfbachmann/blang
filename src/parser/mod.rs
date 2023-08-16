use r#type::Type;

pub mod arg;
pub mod bool;
pub mod bool_lit;
pub mod branch;
pub mod r#break;
pub mod closure;
pub mod cond;
pub mod cont;
pub mod error;
pub mod expr;
pub mod func;
pub mod func_call;
pub mod func_sig;
pub mod i64;
pub mod i64_lit;
pub mod r#loop;
pub mod op;
pub mod program;
pub mod ret;
pub mod statement;
pub mod string;
pub mod string_lit;
pub mod r#struct;
pub mod r#type;
pub mod unresolved;
pub mod var_assign;
pub mod var_dec;
pub mod var_ref;

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Cursor};

    use crate::lexer::kind::TokenKind;
    use crate::lexer::pos::Position;
    use crate::lexer::token::Token;
    use crate::parser::arg::Argument;
    use crate::parser::bool_lit::BoolLit;
    use crate::parser::branch::Branch;
    use crate::parser::closure::Closure;
    use crate::parser::cond::Conditional;
    use crate::parser::error::{ErrorKind, ParseError};
    use crate::parser::expr::Expression;
    use crate::parser::func::Function;
    use crate::parser::func_call::FunctionCall;
    use crate::parser::func_sig::FunctionSignature;
    use crate::parser::i64_lit::I64Lit;
    use crate::parser::op::Operator;
    use crate::parser::program::Program;
    use crate::parser::r#type::Type;
    use crate::parser::ret::Ret;
    use crate::parser::statement::Statement;
    use crate::parser::string_lit::StringLit;
    use crate::parser::var_dec::VariableDeclaration;
    use crate::parser::var_ref::VarRef;

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
            Token::tokenize_line("let i: i64 = 123 let j = 1231", 1).expect("should not error");
        let result = Program::from(&mut tokens).expect("should not error");
        assert_eq!(
            result,
            Program {
                statements: vec![
                    Statement::VariableDeclaration(VariableDeclaration::new(
                        Some(Type::i64()),
                        "i".to_string(),
                        Expression::I64Literal(I64Lit {
                            value: 123,
                            start_pos: Position::new(1, 14),
                            end_pos: Position::new(1, 17),
                        }),
                        Position::new(1, 1),
                        Position::new(1, 17),
                    )),
                    Statement::VariableDeclaration(VariableDeclaration::new(
                        None,
                        "j".to_string(),
                        Expression::I64Literal(I64Lit {
                            value: 1231,
                            start_pos: Position::new(1, 26),
                            end_pos: Position::new(1, 30),
                        }),
                        Position::new(1, 18),
                        Position::new(1, 30),
                    ))
                ]
            }
        );
    }

    #[test]
    fn parse_function_declaration() {
        let mut tokens = Token::tokenize_line(
            r#"fn my_fn(arg1: string, arg2: i64): string { let s = "hello world!"; }"#,
            1,
        )
        .expect("should not error");
        let result = Function::from(&mut tokens).expect("should not error");
        assert_eq!(
            result,
            Function::new(
                FunctionSignature::new(
                    "my_fn",
                    vec![
                        Argument::new("arg1", Type::string()),
                        Argument::new("arg2", Type::i64())
                    ],
                    Some(Type::string()),
                    Position::new(1, 1),
                    Position::new(1, 34),
                ),
                Closure::new(
                    vec![Statement::VariableDeclaration(VariableDeclaration::new(
                        None,
                        "s".to_string(),
                        Expression::StringLiteral(StringLit {
                            value: "hello world!".to_string(),
                            start_pos: Position::new(1, 53),
                            end_pos: Position::new(1, 67),
                        }),
                        Position::new(1, 45),
                        Position::new(1, 67),
                    ))],
                    None,
                    Position::new(1, 43),
                    Position::new(1, 70),
                ),
            )
        );

        let mut tokens = Token::tokenize_line(
            "fn bigboi(f: fn (string, i64): bool, i: i64): fn (bool): string {}",
            1,
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
                                    Argument::new("", Type::string()),
                                    Argument::new("", Type::i64())
                                ],
                                Some(Type::bool()),
                                Position::new(1, 14),
                                Position::new(1, 30),
                            ))),
                        ),
                        Argument::new("i", Type::i64())
                    ],
                    Some(Type::Function(Box::new(FunctionSignature::new_anon(
                        vec![Argument::new("", Type::bool())],
                        Some(Type::string()),
                        Position::new(1, 47),
                        Position::new(1, 56),
                    )))),
                    Position::new(1, 1),
                    Position::new(1, 45),
                ),
                Closure::new(vec![], None, Position::new(1, 65), Position::new(1, 67)),
            )
        );
    }

    #[test]
    fn parse_function_call() {
        let mut tokens =
            Token::tokenize_line(r#"do_thing("one", "two", true)"#, 1).expect("should not error");
        let result = FunctionCall::from(&mut tokens).expect("should not error");
        assert_eq!(
            result,
            FunctionCall::new(
                "do_thing",
                vec![
                    Expression::StringLiteral(StringLit {
                        value: "one".to_string(),
                        start_pos: Position::new(1, 10),
                        end_pos: Position::new(1, 15),
                    }),
                    Expression::StringLiteral(StringLit {
                        value: "two".to_string(),
                        start_pos: Position::new(1, 17),
                        end_pos: Position::new(1, 22),
                    }),
                    Expression::BoolLiteral(BoolLit {
                        value: true,
                        start_pos: Position::new(1, 24),
                        end_pos: Position::new(1, 28),
                    }),
                ],
                Position::new(1, 1),
                Position::new(1, 29),
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
                    start: Position { line: 1, col: 14 },
                    end: Position { line: 1, col: 15 },
                }),
                start_pos: Position { line: 1, col: 14 },
                end_pos: Position { line: 1, col: 15 },
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
                    start: Position { line: 1, col: 15 },
                    end: Position { line: 1, col: 16 },
                }),
                start_pos: Position { line: 1, col: 15 },
                end_pos: Position { line: 1, col: 16 },
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
                kind: ErrorKind::UnexpectedEOF,
                message: _,
                token: None,
                start_pos: Position { line: 1, col: 1 },
                ..
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
                    start: Position { line: 1, col: 4 },
                    end: Position { line: 1, col: 6 },
                }),
                start_pos: Position { line: 1, col: 4 },
                end_pos: Position { line: 1, col: 6 },
            })
        ));
    }

    #[test]
    fn empty_fn_return() {
        let raw = "fn my_func(s: string) {
            if s == \"dog\" {
                return
            }
           
            print(\"not dog\")
        }";
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let result = Program::from(&mut tokens).expect("should not error");
        assert_eq!(
            result,
            Program {
                statements: vec![Statement::FunctionDeclaration(Function::new(
                    FunctionSignature::new(
                        "my_func",
                        vec![Argument::new("s", Type::string())],
                        None,
                        Position::new(1, 1),
                        Position::new(1, 22)
                    ),
                    Closure::new(
                        vec![
                            Statement::Conditional(Conditional::new(vec![Branch::new(
                                Some(Expression::BinaryOperation(
                                    Box::new(Expression::VariableReference(VarRef {
                                        var_name: "s".to_string(),
                                        start_pos: Position::new(2, 16),
                                        end_pos: Position::new(2, 17),
                                    })),
                                    Operator::EqualTo,
                                    Box::new(Expression::StringLiteral(StringLit {
                                        value: "dog".to_string(),
                                        start_pos: Position::new(2, 21),
                                        end_pos: Position::new(2, 26),
                                    })),
                                )),
                                Closure::new(
                                    vec![Statement::Return(Ret::new(
                                        None,
                                        Position::new(3, 17),
                                        Position::new(3, 23)
                                    ))],
                                    None,
                                    Position::new(2, 27),
                                    Position::new(4, 14)
                                ),
                                Position::new(2, 16),
                                Position::new(4, 14),
                            )])),
                            Statement::FunctionCall(FunctionCall::new(
                                "print",
                                vec![Expression::StringLiteral(StringLit {
                                    value: "not dog".to_string(),
                                    start_pos: Position::new(6, 19),
                                    end_pos: Position::new(6, 28),
                                })],
                                Position::new(6, 13),
                                Position::new(6, 29),
                            ))
                        ],
                        None,
                        Position::new(1, 23),
                        Position::new(7, 10),
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
                kind: ErrorKind::UnexpectedEOF,
                message: _,
                token: None,
                ..
            })
        ));
    }
}
