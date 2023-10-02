//! The Blang parser attempts to assemble an AST from the sequence of tokens that the lexer
//! produces.

use r#type::Type;

pub mod arg;
pub mod bool;
pub mod bool_lit;
pub mod branch;
pub mod r#break;
pub mod closure;
pub mod cond;
pub mod r#const;
pub mod cont;
pub mod error;
pub mod expr;
pub mod ext;
pub mod func;
pub mod func_call;
pub mod func_sig;
pub mod i64;
pub mod i64_lit;
pub mod r#impl;
pub mod r#loop;
pub mod member;
pub mod op;
pub mod program;
pub mod ret;
pub mod sizeof;
pub mod statement;
pub mod str;
pub mod str_lit;
pub mod stream;
pub mod r#struct;
pub mod symbol;
pub mod tuple;
pub mod r#type;
pub mod unresolved;
pub mod unsafe_null;
pub mod unsafeptr;
pub mod usize;
pub mod var_assign;
pub mod var_dec;

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Cursor};

    use crate::lexer::pos::Position;
    use crate::lexer::token::Token;
    use crate::lexer::token_kind::TokenKind;
    use crate::parser::arg::Argument;
    use crate::parser::bool::BoolType;
    use crate::parser::bool_lit::BoolLit;
    use crate::parser::branch::Branch;
    use crate::parser::closure::Closure;
    use crate::parser::cond::Conditional;
    use crate::parser::error::{ErrorKind, ParseError};
    use crate::parser::expr::Expression;
    use crate::parser::func::Function;
    use crate::parser::func_call::FunctionCall;
    use crate::parser::func_sig::FunctionSignature;
    use crate::parser::i64::I64Type;
    use crate::parser::i64_lit::I64Lit;
    use crate::parser::op::Operator;
    use crate::parser::program::Program;
    use crate::parser::r#type::Type;
    use crate::parser::ret::Ret;
    use crate::parser::statement::Statement;
    use crate::parser::str::StrType;
    use crate::parser::str_lit::StrLit;
    use crate::parser::stream::Stream;
    use crate::parser::symbol::Symbol;
    use crate::parser::var_dec::VariableDeclaration;

    #[test]
    fn parse_identifier() {
        let tokens = Token::tokenize_line("something", 0).expect("should not error");
        let result =
            Program::parse_identifier(&mut Stream::from(tokens)).expect("should not error");
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
                    fn (n: i64) ~ bool {
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
        fn fib(n: i64, visitor_fn: fn (i64) ~ bool) ~ i64 {
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
        let tokens = Token::tokenize(Cursor::new(raw_code).lines()).expect("should not error");
        Program::from(&mut Stream::from(tokens)).expect("should not error");

        let tokens =
            Token::tokenize_line("let i: i64 = 123 let j = 1231", 1).expect("should not error");
        let result = Program::from(&mut Stream::from(tokens)).expect("should not error");
        assert_eq!(
            result,
            Program {
                statements: vec![
                    Statement::VariableDeclaration(VariableDeclaration::new(
                        Some(Type::i64()),
                        false,
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
                        false,
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
        let tokens = Token::tokenize_line(
            r#"fn my_fn(arg1: str, arg2: i64) ~ str { let s = "hello world!"; }"#,
            1,
        )
        .expect("should not error");
        let result = Function::from(&mut Stream::from(tokens)).expect("should not error");
        assert_eq!(
            result,
            Function::new(
                FunctionSignature::new(
                    "my_fn",
                    vec![
                        Argument::new(
                            "arg1",
                            Type::Str(StrType::new(Position::new(1, 16), Position::new(1, 19))),
                            false,
                            Position::new(1, 10),
                            Position::new(1, 19)
                        ),
                        Argument::new(
                            "arg2",
                            Type::I64(I64Type::new(Position::new(1, 27), Position::new(1, 30))),
                            false,
                            Position::new(1, 21),
                            Position::new(1, 30)
                        )
                    ],
                    Some(Type::Str(StrType::new(
                        Position::new(1, 34),
                        Position::new(1, 37)
                    ))),
                    Position::new(1, 1),
                    Position::new(1, 31),
                ),
                Closure::new(
                    vec![Statement::VariableDeclaration(VariableDeclaration::new(
                        None,
                        false,
                        "s".to_string(),
                        Expression::StrLiteral(StrLit {
                            value: "hello world!".to_string(),
                            start_pos: Position::new(1, 48),
                            end_pos: Position::new(1, 62),
                        }),
                        Position::new(1, 40),
                        Position::new(1, 62),
                    ))],
                    None,
                    Position::new(1, 38),
                    Position::new(1, 65),
                ),
            )
        );

        let tokens = Token::tokenize_line(
            "fn bigboi(f: fn (str, i64) ~ bool, i: i64) ~ fn (bool) ~ str {}",
            1,
        )
        .expect("should not error");
        let result = Function::from(&mut Stream::from(tokens)).expect("should not error");
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
                                    Argument::new(
                                        "",
                                        Type::Str(StrType::new(
                                            Position::new(1, 18),
                                            Position::new(1, 21)
                                        )),
                                        false,
                                        Position::new(1, 18),
                                        Position::new(1, 21)
                                    ),
                                    Argument::new(
                                        "",
                                        Type::I64(I64Type::new(
                                            Position::new(1, 23),
                                            Position::new(1, 26)
                                        )),
                                        false,
                                        Position::new(1, 23),
                                        Position::new(1, 26)
                                    )
                                ],
                                Some(Type::Bool(BoolType::new(
                                    Position::new(1, 30),
                                    Position::new(1, 34)
                                ))),
                                Position::new(1, 14),
                                Position::new(1, 27),
                            ))),
                            false,
                            Position::new(1, 11),
                            Position::new(1, 27),
                        ),
                        Argument::new(
                            "i",
                            Type::I64(I64Type::new(Position::new(1, 39), Position::new(1, 42))),
                            false,
                            Position::new(1, 36),
                            Position::new(1, 42)
                        )
                    ],
                    Some(Type::Function(Box::new(FunctionSignature::new_anon(
                        vec![Argument::new(
                            "",
                            Type::Bool(BoolType::new(Position::new(1, 50), Position::new(1, 54))),
                            false,
                            Position::new(1, 50),
                            Position::new(1, 54)
                        )],
                        Some(Type::Str(StrType::new(
                            Position::new(1, 58),
                            Position::new(1, 61)
                        ))),
                        Position::new(1, 46),
                        Position::new(1, 55),
                    )))),
                    Position::new(1, 1),
                    Position::new(1, 43),
                ),
                Closure::new(vec![], None, Position::new(1, 62), Position::new(1, 64)),
            )
        );
    }

    #[test]
    fn parse_function_call() {
        let tokens =
            Token::tokenize_line(r#"do_thing("one", "two", true)"#, 1).expect("should not error");
        let result =
            FunctionCall::from_single(&mut Stream::from(tokens)).expect("should not error");
        assert_eq!(
            result,
            FunctionCall::new(
                Symbol::new("do_thing", Position::new(1, 1), Position::new(1, 9)),
                vec![
                    Expression::StrLiteral(StrLit {
                        value: "one".to_string(),
                        start_pos: Position::new(1, 10),
                        end_pos: Position::new(1, 15),
                    }),
                    Expression::StrLiteral(StrLit {
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
        let tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let result = Program::from(&mut Stream::from(tokens));
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::ExpectedBinOpOrEndOfExpr,
                message: _,
                token: Some(Token {
                    kind: TokenKind::LeftParen,
                    start: Position { line: 1, col: 13 },
                    end: Position { line: 1, col: 14 },
                }),
                start_pos: Position { line: 1, col: 13 },
                end_pos: Position { line: 1, col: 14 },
            })
        ));
    }

    #[test]
    fn invalid_extra_close_paren() {
        let raw = r#"let i = call())"#;
        let tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let result = Program::from(&mut Stream::from(tokens));
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
        let tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let result = Program::from(&mut Stream::from(tokens));
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
        let tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let result = Program::from(&mut Stream::from(tokens));
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
        let raw = "fn my_func(s: str) {
            if s == \"dog\" {
                return
            }
           
            print(\"not dog\")
        }";
        let tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let result = Program::from(&mut Stream::from(tokens)).expect("should not error");
        assert_eq!(
            result,
            Program {
                statements: vec![Statement::FunctionDeclaration(Function::new(
                    FunctionSignature::new(
                        "my_func",
                        vec![Argument::new(
                            "s",
                            Type::Str(StrType::new(Position::new(1, 15), Position::new(1, 18))),
                            false,
                            Position::new(1, 12),
                            Position::new(1, 18)
                        )],
                        None,
                        Position::new(1, 1),
                        Position::new(1, 19)
                    ),
                    Closure::new(
                        vec![
                            Statement::Conditional(Conditional::new(vec![Branch::new(
                                Some(Expression::BinaryOperation(
                                    Box::new(Expression::Symbol(Symbol {
                                        name: "s".to_string(),
                                        member_access: None,
                                        start_pos: Position::new(2, 16),
                                        end_pos: Position::new(2, 17),
                                    })),
                                    Operator::EqualTo,
                                    Box::new(Expression::StrLiteral(StrLit {
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
                                Symbol::new("print", Position::new(6, 13), Position::new(6, 18)),
                                vec![Expression::StrLiteral(StrLit {
                                    value: "not dog".to_string(),
                                    start_pos: Position::new(6, 19),
                                    end_pos: Position::new(6, 28),
                                })],
                                Position::new(6, 13),
                                Position::new(6, 29),
                            ))
                        ],
                        None,
                        Position::new(1, 20),
                        Position::new(7, 10),
                    )
                ))]
            }
        );
    }

    #[test]
    fn missing_fn_closing_brace() {
        let raw = r#"fn thing() ~ i64 {
            return 4 / 2 + 8
        "#;
        let tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        let result = Program::from(&mut Stream::from(tokens));
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
