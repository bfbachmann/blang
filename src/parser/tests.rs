#[cfg(test)]
mod tests {
    use crate::lexer::lex::lex;
    use crate::lexer::pos::Position;
    use crate::lexer::stream::Stream;
    use crate::lexer::token::Token;
    use crate::lexer::token_kind::TokenKind;
    use crate::parser::ast::arg::Argument;
    use crate::parser::ast::bool_lit::BoolLit;
    use crate::parser::ast::branch::Branch;
    use crate::parser::ast::closure::Closure;
    use crate::parser::ast::cond::Conditional;
    use crate::parser::ast::expr::Expression;
    use crate::parser::ast::func::Function;
    use crate::parser::ast::func_call::FunctionCall;
    use crate::parser::ast::func_sig::FunctionSignature;
    use crate::parser::ast::i64_lit::I64Lit;
    use crate::parser::ast::op::Operator;
    use crate::parser::ast::r#type::Type;
    use crate::parser::ast::ret::Ret;
    use crate::parser::ast::statement::Statement;
    use crate::parser::ast::str_lit::StrLit;
    use crate::parser::ast::symbol::Symbol;
    use crate::parser::ast::unresolved::UnresolvedType;
    use crate::parser::ast::var_dec::VariableDeclaration;
    use crate::parser::error::{ErrorKind, ParseError};
    use crate::parser::source::Source;

    fn tokenize(code: &str) -> Vec<Token> {
        lex(&mut Stream::from(code.chars().collect())).expect("should succeed")
    }

    #[test]
    fn parse_identifier() {
        let tokens = tokenize("something");
        let result = Source::parse_identifier(&mut Stream::from(tokens)).expect("should not error");
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
        let tokens = tokenize(raw_code);
        Source::from("", &mut Stream::from(tokens)).expect("should not error");

        let tokens = tokenize("let i: i64 = 123 let j = 1231");
        let result = Source::from("", &mut Stream::from(tokens)).expect("should not error");
        assert_eq!(
            result,
            Source {
                path: "".to_string(),
                statements: vec![
                    Statement::VariableDeclaration(VariableDeclaration::new(
                        Some(Type::new_unresolved("i64")),
                        false,
                        "i".to_string(),
                        Expression::I64Literal(I64Lit {
                            value: 123,
                            has_type_suffix: false,
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
                            has_type_suffix: false,
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
        let tokens =
            tokenize(r#"fn my_fn(arg1: str, arg2: i64) ~ str { let s = "hello world!"; }"#);
        let result = Function::from(&mut Stream::from(tokens)).expect("should not error");
        assert_eq!(
            result,
            Function::new(
                FunctionSignature::new(
                    "my_fn",
                    vec![
                        Argument::new(
                            "arg1",
                            Type::Unresolved(UnresolvedType::new(
                                "str",
                                Position::new(1, 16),
                                Position::new(1, 19)
                            )),
                            false,
                            Position::new(1, 10),
                            Position::new(1, 19)
                        ),
                        Argument::new(
                            "arg2",
                            Type::Unresolved(UnresolvedType::new(
                                "i64",
                                Position::new(1, 27),
                                Position::new(1, 30)
                            )),
                            false,
                            Position::new(1, 21),
                            Position::new(1, 30)
                        )
                    ],
                    Some(Type::Unresolved(UnresolvedType::new(
                        "str",
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

        let tokens = tokenize("fn bigboi(f: fn (str, i64) ~ bool, i: i64) ~ fn (bool) ~ str {}");
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
                                        Type::Unresolved(UnresolvedType::new(
                                            "str",
                                            Position::new(1, 18),
                                            Position::new(1, 21)
                                        )),
                                        false,
                                        Position::new(1, 18),
                                        Position::new(1, 21)
                                    ),
                                    Argument::new(
                                        "",
                                        Type::Unresolved(UnresolvedType::new(
                                            "i64",
                                            Position::new(1, 23),
                                            Position::new(1, 26)
                                        )),
                                        false,
                                        Position::new(1, 23),
                                        Position::new(1, 26)
                                    )
                                ],
                                Some(Type::Unresolved(UnresolvedType::new(
                                    "bool",
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
                            Type::Unresolved(UnresolvedType::new(
                                "i64",
                                Position::new(1, 39),
                                Position::new(1, 42)
                            )),
                            false,
                            Position::new(1, 36),
                            Position::new(1, 42)
                        )
                    ],
                    Some(Type::Function(Box::new(FunctionSignature::new_anon(
                        vec![Argument::new(
                            "",
                            Type::Unresolved(UnresolvedType::new(
                                "bool",
                                Position::new(1, 50),
                                Position::new(1, 54)
                            )),
                            false,
                            Position::new(1, 50),
                            Position::new(1, 54)
                        )],
                        Some(Type::Unresolved(UnresolvedType::new(
                            "str",
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
        let tokens = tokenize(r#"do_thing("one", "two", true)"#);
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
        let mut char_stream = Stream::from(raw.chars().collect());
        let tokens = lex(&mut char_stream).expect("should not error");
        let result = Source::from("", &mut Stream::from(tokens));
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
        let mut char_stream = Stream::from(raw.chars().collect());
        let tokens = lex(&mut char_stream).expect("should not error");
        let result = Source::from("", &mut Stream::from(tokens));
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
        let raw = r#"do(((x+3) > 2) or other"#;
        let mut char_stream = Stream::from(raw.chars().collect());
        let tokens = lex(&mut char_stream).expect("should not error");
        let result = Source::from("", &mut Stream::from(tokens));
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
        let raw = r#"do(and true)"#;
        let mut char_stream = Stream::from(raw.chars().collect());
        let tokens = lex(&mut char_stream).expect("should not error");
        let result = Source::from("", &mut Stream::from(tokens));
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::UnexpectedOperator,
                message: _,
                token: Some(Token {
                    kind: TokenKind::LogicalAnd,
                    start: Position { line: 1, col: 4 },
                    end: Position { line: 1, col: 7 },
                }),
                start_pos: Position { line: 1, col: 4 },
                end_pos: Position { line: 1, col: 7 },
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
        let mut char_stream = Stream::from(raw.chars().collect());
        let tokens = lex(&mut char_stream).expect("should not error");
        let result = Source::from("", &mut Stream::from(tokens)).expect("should not error");
        assert_eq!(
            result,
            Source {
                path: "".to_string(),
                statements: vec![Statement::FunctionDeclaration(Function::new(
                    FunctionSignature::new(
                        "my_func",
                        vec![Argument::new(
                            "s",
                            Type::Unresolved(UnresolvedType::new(
                                "str",
                                Position::new(1, 15),
                                Position::new(1, 18)
                            )),
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
        let mut char_stream = Stream::from(raw.chars().collect());
        let tokens = lex(&mut char_stream).expect("should not error");
        let result = Source::from("", &mut Stream::from(tokens));
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

    #[test]
    fn parse_var_assignment() {
        let input = "let thing: i64 = 234";
        let tokens = lex(&mut Stream::from(input.chars().collect())).expect("should succeed");
        Statement::from(&mut Stream::from(tokens)).expect("should not error");
    }

    #[test]
    fn inline_struct_types_in_fn_sig() {
        let input = r#"fn one(a: struct {one: i64, two: bool}, b: i64) ~ struct {thing: str} {}"#;
        let tokens = lex(&mut Stream::from(input.chars().collect())).expect("should succeed");
        let result = Source::from("", &mut Stream::from(tokens));
        assert!(matches!(result, Ok(_)));
    }

    #[test]
    fn invalid_type_cast() {
        let input = r#"
            fn main() {
                let a = 5u64
                let b = a as 543
            }
        "#;
        let tokens = lex(&mut Stream::from(input.chars().collect())).expect("should succeed");
        let result = Source::from("", &mut Stream::from(tokens));
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::ExpectedType,
                ..
            })
        ))
    }
}
