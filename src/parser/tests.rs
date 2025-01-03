#[cfg(test)]
mod tests {
    use crate::lexer::lex::lex;
    use crate::lexer::pos::{Position, Span};
    use crate::lexer::stream::Stream;
    use crate::lexer::token::Token;
    use crate::lexer::token_kind::TokenKind;
    use crate::parser::ast::arg::Argument;
    use crate::parser::ast::bool_lit::BoolLit;
    use crate::parser::ast::branch::Branch;
    use crate::parser::ast::closure::Closure;
    use crate::parser::ast::cond::Conditional;
    use crate::parser::ast::expr::{parse_expr, Expression};
    use crate::parser::ast::func::Function;
    use crate::parser::ast::func_call::FnCall;
    use crate::parser::ast::func_sig::FunctionSignature;
    use crate::parser::ast::int_lit::IntLit;
    use crate::parser::ast::op::Operator;
    use crate::parser::ast::r#type::Type;
    use crate::parser::ast::ret::Ret;
    use crate::parser::ast::statement::Statement;
    use crate::parser::ast::str_lit::StrLit;
    use crate::parser::ast::symbol::Symbol;
    use crate::parser::ast::unresolved::UnresolvedType;
    use crate::parser::ast::var_assign::VariableAssignment;
    use crate::parser::ast::var_dec::VariableDeclaration;
    use crate::parser::error::{ErrorKind, ParseError};
    use crate::parser::module::Module;

    fn tokenize(code: &str) -> Vec<Token> {
        lex(code).expect("should succeed")
    }

    #[test]
    fn parse_identifier() {
        let tokens = tokenize("something");
        let result = Module::parse_identifier(&mut Stream::from(tokens)).expect("should not error");
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
                    fn (n: int) -> bool {
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
        fn fib(n: int, visitor_fn: fn (int) -> bool) -> int {
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
        Module::from("", &mut Stream::from(tokens)).expect("should not error");

        let tokens = tokenize("let i: i64 = 123 let j = 1231");
        let result = Module::from("", &mut Stream::from(tokens)).expect("should not error");
        assert_eq!(
            result,
            Module {
                path: "".to_string(),
                used_mods: vec![],
                statements: vec![
                    Statement::VariableDeclaration(VariableDeclaration::new(
                        Some(Type::new_unresolved("i64")),
                        false,
                        "i".to_string(),
                        Expression::IntLiteral(IntLit {
                            value: 123,
                            has_suffix: false,
                            span: Span {
                                start_pos: Position::new(1, 14),
                                end_pos: Position::new(1, 17),
                            }
                        }),
                        Span {
                            start_pos: Position::new(1, 1),
                            end_pos: Position::new(1, 17),
                        }
                    )),
                    Statement::VariableDeclaration(VariableDeclaration::new(
                        None,
                        false,
                        "j".to_string(),
                        Expression::IntLiteral(IntLit {
                            value: 1231,
                            has_suffix: false,
                            span: Span {
                                start_pos: Position::new(1, 26),
                                end_pos: Position::new(1, 30),
                            }
                        }),
                        Span {
                            start_pos: Position::new(1, 18),
                            end_pos: Position::new(1, 30),
                        }
                    ))
                ]
            }
        );
    }

    #[test]
    fn parse_function_declaration() {
        let tokens =
            tokenize(r#"fn my_fn(arg1: str, arg2: i64) -> str { let s = "hello world!"; }"#);
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
                                Span {
                                    start_pos: Position::new(1, 16),
                                    end_pos: Position::new(1, 19)
                                }
                            )),
                            false,
                            Span {
                                start_pos: Position::new(1, 10),
                                end_pos: Position::new(1, 19)
                            }
                        ),
                        Argument::new(
                            "arg2",
                            Type::Unresolved(UnresolvedType::new(
                                "i64",
                                Span {
                                    start_pos: Position::new(1, 27),
                                    end_pos: Position::new(1, 30)
                                }
                            )),
                            false,
                            Span {
                                start_pos: Position::new(1, 21),
                                end_pos: Position::new(1, 30)
                            }
                        )
                    ],
                    Some(Type::Unresolved(UnresolvedType::new(
                        "str",
                        Span {
                            start_pos: Position::new(1, 35),
                            end_pos: Position::new(1, 38)
                        }
                    ))),
                    Span {
                        start_pos: Position::new(1, 1),
                        end_pos: Position::new(1, 38),
                    }
                ),
                Closure::new(
                    vec![Statement::VariableDeclaration(VariableDeclaration::new(
                        None,
                        false,
                        "s".to_string(),
                        Expression::StrLiteral(StrLit {
                            value: "hello world!".to_string(),
                            span: Span {
                                start_pos: Position::new(1, 49),
                                end_pos: Position::new(1, 63),
                            }
                        }),
                        Span {
                            start_pos: Position::new(1, 41),
                            end_pos: Position::new(1, 63),
                        }
                    ))],
                    Span {
                        start_pos: Position::new(1, 39),
                        end_pos: Position::new(1, 66),
                    }
                ),
                false
            )
        );

        let tokens = tokenize("fn bigboi(f: fn (str, i64) -> bool, i: i64) -> fn (bool) -> str {}");
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
                                            Span {
                                                start_pos: Position::new(1, 18),
                                                end_pos: Position::new(1, 21)
                                            }
                                        )),
                                        false,
                                        Span {
                                            start_pos: Position::new(1, 18),
                                            end_pos: Position::new(1, 21)
                                        }
                                    ),
                                    Argument::new(
                                        "",
                                        Type::Unresolved(UnresolvedType::new(
                                            "i64",
                                            Span {
                                                start_pos: Position::new(1, 23),
                                                end_pos: Position::new(1, 26)
                                            }
                                        )),
                                        false,
                                        Span {
                                            start_pos: Position::new(1, 23),
                                            end_pos: Position::new(1, 26)
                                        }
                                    )
                                ],
                                Some(Type::Unresolved(UnresolvedType::new(
                                    "bool",
                                    Span {
                                        start_pos: Position::new(1, 31),
                                        end_pos: Position::new(1, 35)
                                    }
                                ))),
                                Span {
                                    start_pos: Position::new(1, 14),
                                    end_pos: Position::new(1, 35),
                                }
                            ))),
                            false,
                            Span {
                                start_pos: Position::new(1, 11),
                                end_pos: Position::new(1, 35),
                            }
                        ),
                        Argument::new(
                            "i",
                            Type::Unresolved(UnresolvedType::new(
                                "i64",
                                Span {
                                    start_pos: Position::new(1, 40),
                                    end_pos: Position::new(1, 43)
                                }
                            )),
                            false,
                            Span {
                                start_pos: Position::new(1, 37),
                                end_pos: Position::new(1, 43)
                            }
                        )
                    ],
                    Some(Type::Function(Box::new(FunctionSignature::new_anon(
                        vec![Argument::new(
                            "",
                            Type::Unresolved(UnresolvedType::new(
                                "bool",
                                Span {
                                    start_pos: Position::new(1, 52),
                                    end_pos: Position::new(1, 56)
                                }
                            )),
                            false,
                            Span {
                                start_pos: Position::new(1, 52),
                                end_pos: Position::new(1, 56)
                            }
                        )],
                        Some(Type::Unresolved(UnresolvedType::new(
                            "str",
                            Span {
                                start_pos: Position::new(1, 61),
                                end_pos: Position::new(1, 64)
                            }
                        ))),
                        Span {
                            start_pos: Position::new(1, 48),
                            end_pos: Position::new(1, 64),
                        }
                    )))),
                    Span {
                        start_pos: Position::new(1, 1),
                        end_pos: Position::new(1, 64),
                    }
                ),
                Closure::new(
                    vec![],
                    Span {
                        start_pos: Position::new(1, 65),
                        end_pos: Position::new(1, 67)
                    }
                ),
                false
            )
        );
    }

    #[test]
    fn parse_function_call() {
        let tokens = tokenize(r#"do_thing("one", "two", true)"#);
        let result = parse_expr(&mut Stream::from(tokens)).expect("should not error");
        assert_eq!(
            result,
            Expression::FunctionCall(Box::new(FnCall::new(
                Expression::Symbol(Symbol::new(
                    "do_thing",
                    Span {
                        start_pos: Position::new(1, 1),
                        end_pos: Position::new(1, 9),
                    },
                )),
                vec![
                    Expression::StrLiteral(StrLit {
                        value: "one".to_string(),
                        span: Span {
                            start_pos: Position::new(1, 10),
                            end_pos: Position::new(1, 15),
                        }
                    }),
                    Expression::StrLiteral(StrLit {
                        value: "two".to_string(),
                        span: Span {
                            start_pos: Position::new(1, 17),
                            end_pos: Position::new(1, 22),
                        }
                    }),
                    Expression::BoolLiteral(BoolLit {
                        value: true,
                        span: Span {
                            start_pos: Position::new(1, 24),
                            end_pos: Position::new(1, 28),
                        },
                    }),
                ],
                Position::new(1, 29),
            )))
        );
    }

    #[test]
    fn invalid_extra_comma() {
        let raw = r#"let i = call(,,)"#;
        let tokens = lex(raw).expect("should not error");
        let result = Module::from("", &mut Stream::from(tokens));
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::ExpectedExpr,
                message: _,
                token: Some(Token {
                    kind: TokenKind::Comma,
                    span: Span {
                        start_pos: Position { line: 1, col: 14 },
                        end_pos: Position { line: 1, col: 15 },
                    }
                }),
                span: Span {
                    start_pos: Position { line: 1, col: 14 },
                    end_pos: Position { line: 1, col: 15 },
                }
            })
        ));
    }

    #[test]
    fn invalid_extra_close_paren() {
        let raw = r#"let i = call())"#;
        let tokens = lex(raw).expect("should not error");
        let result = Module::from("", &mut Stream::from(tokens));
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::ExpectedStatement,
                message: _,
                token: Some(Token {
                    kind: TokenKind::RightParen,
                    span: Span {
                        start_pos: Position { line: 1, col: 15 },
                        end_pos: Position { line: 1, col: 16 },
                    }
                }),
                span: Span {
                    start_pos: Position { line: 1, col: 15 },
                    end_pos: Position { line: 1, col: 16 },
                }
            })
        ));
    }

    #[test]
    fn invalid_missing_close_paren() {
        let raw = r#"do(((x+3) > 2) || other"#;
        let tokens = lex(raw).expect("should not error");
        let result = Module::from("", &mut Stream::from(tokens));
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
    fn invalid_start_of_expression() {
        let raw = r#"do(&& true)"#;
        let tokens = lex(raw).expect("should not error");
        let result = Module::from("", &mut Stream::from(tokens));
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::ExpectedBeginExpr,
                message: _,
                token: Some(Token {
                    kind: TokenKind::LogicalAnd,
                    span: Span {
                        start_pos: Position { line: 1, col: 4 },
                        end_pos: Position { line: 1, col: 6 },
                    }
                }),
                span: Span {
                    start_pos: Position { line: 1, col: 4 },
                    end_pos: Position { line: 1, col: 6 },
                }
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
        let tokens = lex(raw).expect("should not error");
        let result = Module::from("", &mut Stream::from(tokens)).expect("should not error");
        assert_eq!(
            result,
            Module {
                path: "".to_string(),
                used_mods: vec![],
                statements: vec![Statement::FunctionDeclaration(Function::new(
                    FunctionSignature::new(
                        "my_func",
                        vec![Argument::new(
                            "s",
                            Type::Unresolved(UnresolvedType::new(
                                "str",
                                Span {
                                    start_pos: Position::new(1, 15),
                                    end_pos: Position::new(1, 18)
                                }
                            )),
                            false,
                            Span {
                                start_pos: Position::new(1, 12),
                                end_pos: Position::new(1, 18)
                            }
                        )],
                        None,
                        Span {
                            start_pos: Position::new(1, 1),
                            end_pos: Position::new(1, 19)
                        }
                    ),
                    Closure::new(
                        vec![
                            Statement::Conditional(Conditional::new(vec![Branch::new(
                                Some(Expression::BinaryOperation(
                                    Box::new(Expression::Symbol(Symbol {
                                        maybe_mod_name: None,
                                        name: "s".to_string(),
                                        params: vec![],
                                        span: Span {
                                            start_pos: Position::new(2, 16),
                                            end_pos: Position::new(2, 17),
                                        },
                                    })),
                                    Operator::EqualTo,
                                    Box::new(Expression::StrLiteral(StrLit {
                                        value: "dog".to_string(),
                                        span: Span {
                                            start_pos: Position::new(2, 21),
                                            end_pos: Position::new(2, 26),
                                        }
                                    })),
                                )),
                                Closure::new(
                                    vec![Statement::Return(Ret::new(
                                        None,
                                        Span {
                                            start_pos: Position::new(3, 17),
                                            end_pos: Position::new(3, 23)
                                        },
                                    ))],
                                    Span {
                                        start_pos: Position::new(2, 27),
                                        end_pos: Position::new(4, 14)
                                    },
                                ),
                                Span {
                                    start_pos: Position::new(2, 16),
                                    end_pos: Position::new(4, 14),
                                }
                            )])),
                            Statement::FunctionCall(FnCall::new(
                                Expression::Symbol(Symbol::new(
                                    "print",
                                    Span {
                                        start_pos: Position::new(6, 13),
                                        end_pos: Position::new(6, 18)
                                    },
                                )),
                                vec![Expression::StrLiteral(StrLit {
                                    value: "not dog".to_string(),
                                    span: Span {
                                        start_pos: Position::new(6, 19),
                                        end_pos: Position::new(6, 28),
                                    }
                                })],
                                Position::new(6, 29),
                            ))
                        ],
                        Span {
                            start_pos: Position::new(1, 20),
                            end_pos: Position::new(7, 10),
                        },
                    ),
                    false
                ))]
            }
        );
    }

    #[test]
    fn missing_fn_closing_brace() {
        let raw = r#"fn thing() -> i64 {
            return 4 / 2 + 8
        "#;
        let tokens = lex(raw).expect("should not error");
        let result = Module::from("", &mut Stream::from(tokens));
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
        let raw = "let thing: i64 = 234";
        let tokens = lex(raw).expect("should succeed");
        Statement::from(&mut Stream::from(tokens)).expect("should not error");
    }

    #[test]
    fn invalid_type_cast() {
        let raw = r#"
            fn main() {
                let a = 5u64
                let b = a as 543
            }
        "#;
        let tokens = lex(raw).expect("should succeed");
        let result = Module::from("", &mut Stream::from(tokens));
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::ExpectedIdent,
                ..
            })
        ))
    }

    #[test]
    fn parenthesized_assign_after_expr() {
        let raw = r#"
            let a = thing
            (thing) = 2
        "#;
        let tokens = lex(raw).expect("should succeed");
        let result = Module::from("", &mut Stream::from(tokens));
        assert_eq!(
            result.unwrap().statements,
            vec![
                Statement::VariableDeclaration(VariableDeclaration {
                    maybe_type: None,
                    is_mut: false,
                    name: "a".to_string(),
                    value: Expression::Symbol(Symbol {
                        maybe_mod_name: None,
                        name: "thing".to_string(),
                        params: vec![],
                        span: Span {
                            start_pos: Position::new(2, 21),
                            end_pos: Position::new(2, 26),
                        }
                    }),
                    span: Span {
                        start_pos: Position::new(2, 13),
                        end_pos: Position::new(2, 26),
                    },
                }),
                Statement::VariableAssignment(VariableAssignment::new(
                    Expression::Symbol(Symbol {
                        maybe_mod_name: None,
                        name: "thing".to_string(),
                        params: vec![],
                        span: Span {
                            start_pos: Position::new(3, 14),
                            end_pos: Position::new(3, 19),
                        },
                    }),
                    Expression::IntLiteral(IntLit {
                        value: 2,
                        has_suffix: false,
                        span: Span {
                            start_pos: Position::new(3, 23),
                            end_pos: Position::new(3, 24),
                        }
                    }),
                    Position::new(3, 13),
                ))
            ]
        )
    }

    #[test]
    fn invalid_mod_paths() {
        for path in ["/thing.bl", "../thing.bl", "path/../table.bl"] {
            let raw = format!(r#"use thing: "{path}""#);
            let tokens = lex(raw.as_str()).expect("should succeed");
            let result = Module::from("", &mut Stream::from(tokens));
            assert!(matches!(
                result,
                Err(ParseError {
                    kind: ErrorKind::InvalidModPath,
                    ..
                })
            ));
        }
    }
}
