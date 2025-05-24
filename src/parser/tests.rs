#[cfg(test)]
mod tests {
    use crate::lexer::lex;
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
    use crate::parser::ast::mod_::ModDecl;
    use crate::parser::ast::op::Operator;
    use crate::parser::ast::r#type::Type;
    use crate::parser::ast::ret::Ret;
    use crate::parser::ast::statement::Statement;
    use crate::parser::ast::str_lit::StrLit;
    use crate::parser::ast::symbol::{Name, Symbol};
    use crate::parser::ast::unresolved::UnresolvedType;
    use crate::parser::ast::var_assign::VariableAssignment;
    use crate::parser::ast::var_dec::VariableDeclaration;
    use crate::parser::error::{ErrorKind, ParseError, ParseResult};
    use crate::parser::file_parser::FileParser;
    use crate::parser::src_file::SrcFile;

    fn new_parser(code: &str) -> FileParser {
        let tokens = lex(code, 0).expect("should succeed");
        FileParser::new(0, Stream::new(tokens))
    }

    fn parse(code: &str) -> ParseResult<SrcFile> {
        let mut parser = new_parser(code);
        SrcFile::parse(&mut parser)
    }

    #[test]
    fn parse_program() {
        let raw_code = r#"
        mod main

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
        parse(raw_code).expect("should not error");

        let raw_code = "mod main let i: i64 = 123 let j = 1231";
        let result = parse(raw_code).expect("should not error");
        assert_eq!(
            result,
            SrcFile {
                id: 0,
                mod_decl: ModDecl {
                    name: "main".to_string(),
                    span: Span {
                        file_id: 0,
                        start_pos: Position::new(1, 1),
                        end_pos: Position::new(1, 9),
                    },
                },
                used_mods: vec![],
                statements: vec![
                    Statement::VariableDeclaration(VariableDeclaration::new(
                        Some(Type::Unresolved(UnresolvedType::new(
                            Name {
                                value: "i64".to_string(),
                                span: Span {
                                    file_id: 0,
                                    start_pos: Position::new(1, 17),
                                    end_pos: Position::new(1, 20),
                                },
                            },
                            Span {
                                file_id: 0,
                                start_pos: Position::new(1, 17),
                                end_pos: Position::new(1, 20),
                            }
                        ))),
                        false,
                        Name {
                            value: "i".to_string(),
                            span: Span {
                                file_id: 0,
                                start_pos: Position::new(1, 14),
                                end_pos: Position::new(1, 15),
                            }
                        },
                        Expression::IntLiteral(IntLit {
                            value: 123,
                            has_suffix: false,
                            span: Span {
                                file_id: 0,
                                start_pos: Position::new(1, 23),
                                end_pos: Position::new(1, 26),
                            }
                        }),
                        Span {
                            file_id: 0,
                            start_pos: Position::new(1, 10),
                            end_pos: Position::new(1, 26),
                        }
                    )),
                    Statement::VariableDeclaration(VariableDeclaration::new(
                        None,
                        false,
                        Name {
                            value: "j".to_string(),
                            span: Span {
                                file_id: 0,
                                start_pos: Position::new(1, 31),
                                end_pos: Position::new(1, 32),
                            }
                        },
                        Expression::IntLiteral(IntLit {
                            value: 1231,
                            has_suffix: false,
                            span: Span {
                                file_id: 0,
                                start_pos: Position::new(1, 35),
                                end_pos: Position::new(1, 39),
                            }
                        }),
                        Span {
                            file_id: 0,
                            start_pos: Position::new(1, 27),
                            end_pos: Position::new(1, 39),
                        }
                    ))
                ]
            }
        );
    }

    #[test]
    fn parse_function_declaration() {
        let mut parser =
            new_parser(r#"fn my_fn(arg1: str, arg2: i64) -> str { let s = "hello world!"; }"#);
        let result = Function::parse(&mut parser).expect("should not error");
        assert_eq!(
            result,
            Function::new(
                FunctionSignature::new(
                    Name {
                        value: "my_fn".to_string(),
                        span: Span {
                            file_id: 0,
                            start_pos: Position::new(1, 4),
                            end_pos: Position::new(1, 9)
                        }
                    },
                    vec![
                        Argument::new(
                            "arg1",
                            Type::Unresolved(UnresolvedType::new(
                                Name {
                                    value: "str".to_string(),
                                    span: Span {
                                        file_id: 0,
                                        start_pos: Position::new(1, 16),
                                        end_pos: Position::new(1, 19)
                                    },
                                },
                                Span {
                                    file_id: 0,
                                    start_pos: Position::new(1, 16),
                                    end_pos: Position::new(1, 19)
                                }
                            )),
                            false,
                            Span {
                                file_id: 0,
                                start_pos: Position::new(1, 10),
                                end_pos: Position::new(1, 19)
                            }
                        ),
                        Argument::new(
                            "arg2",
                            Type::Unresolved(UnresolvedType::new(
                                Name {
                                    value: "i64".to_string(),
                                    span: Span {
                                        file_id: 0,
                                        start_pos: Position::new(1, 27),
                                        end_pos: Position::new(1, 30)
                                    },
                                },
                                Span {
                                    file_id: 0,
                                    start_pos: Position::new(1, 27),
                                    end_pos: Position::new(1, 30)
                                }
                            )),
                            false,
                            Span {
                                file_id: 0,
                                start_pos: Position::new(1, 21),
                                end_pos: Position::new(1, 30)
                            }
                        )
                    ],
                    Some(Type::Unresolved(UnresolvedType::new(
                        Name {
                            value: "str".to_string(),
                            span: Span {
                                file_id: 0,
                                start_pos: Position::new(1, 35),
                                end_pos: Position::new(1, 38)
                            },
                        },
                        Span {
                            file_id: 0,
                            start_pos: Position::new(1, 35),
                            end_pos: Position::new(1, 38)
                        }
                    ))),
                    Span {
                        file_id: 0,
                        start_pos: Position::new(1, 1),
                        end_pos: Position::new(1, 38),
                    }
                ),
                Closure::new(
                    vec![Statement::VariableDeclaration(VariableDeclaration::new(
                        None,
                        false,
                        Name {
                            value: "s".to_string(),
                            span: Span {
                                file_id: 0,
                                start_pos: Position::new(1, 45),
                                end_pos: Position::new(1, 46),
                            }
                        },
                        Expression::StrLiteral(StrLit {
                            value: "hello world!".to_string(),
                            span: Span {
                                file_id: 0,
                                start_pos: Position::new(1, 49),
                                end_pos: Position::new(1, 63),
                            }
                        }),
                        Span {
                            file_id: 0,
                            start_pos: Position::new(1, 41),
                            end_pos: Position::new(1, 63),
                        }
                    ))],
                    Span {
                        file_id: 0,
                        start_pos: Position::new(1, 39),
                        end_pos: Position::new(1, 66),
                    }
                ),
                false
            )
        );

        let mut parser =
            new_parser("fn bigboi(f: fn (str, i64) -> bool, i: i64) -> fn (bool) -> str {}");
        let result = Function::parse(&mut parser).expect("should not error");
        assert_eq!(
            result,
            Function::new(
                FunctionSignature::new(
                    Name {
                        value: "bigboi".to_string(),
                        span: Span {
                            file_id: 0,
                            start_pos: Position::new(1, 4),
                            end_pos: Position::new(1, 10)
                        },
                    },
                    vec![
                        Argument::new(
                            "f",
                            Type::Function(Box::new(FunctionSignature::new_anon(
                                vec![
                                    Argument::new(
                                        "",
                                        Type::Unresolved(UnresolvedType::new(
                                            Name {
                                                value: "str".to_string(),
                                                span: Span {
                                                    file_id: 0,
                                                    start_pos: Position::new(1, 18),
                                                    end_pos: Position::new(1, 21)
                                                },
                                            },
                                            Span {
                                                file_id: 0,
                                                start_pos: Position::new(1, 18),
                                                end_pos: Position::new(1, 21)
                                            }
                                        )),
                                        false,
                                        Span {
                                            file_id: 0,
                                            start_pos: Position::new(1, 18),
                                            end_pos: Position::new(1, 21)
                                        }
                                    ),
                                    Argument::new(
                                        "",
                                        Type::Unresolved(UnresolvedType::new(
                                            Name {
                                                value: "i64".to_string(),
                                                span: Span {
                                                    file_id: 0,
                                                    start_pos: Position::new(1, 23),
                                                    end_pos: Position::new(1, 26)
                                                },
                                            },
                                            Span {
                                                file_id: 0,
                                                start_pos: Position::new(1, 23),
                                                end_pos: Position::new(1, 26)
                                            }
                                        )),
                                        false,
                                        Span {
                                            file_id: 0,
                                            start_pos: Position::new(1, 23),
                                            end_pos: Position::new(1, 26)
                                        }
                                    )
                                ],
                                Some(Type::Unresolved(UnresolvedType::new(
                                    Name {
                                        value: "bool".to_string(),
                                        span: Span {
                                            file_id: 0,
                                            start_pos: Position::new(1, 31),
                                            end_pos: Position::new(1, 35)
                                        },
                                    },
                                    Span {
                                        file_id: 0,
                                        start_pos: Position::new(1, 31),
                                        end_pos: Position::new(1, 35)
                                    }
                                ))),
                                Span {
                                    file_id: 0,
                                    start_pos: Position::new(1, 14),
                                    end_pos: Position::new(1, 35),
                                }
                            ))),
                            false,
                            Span {
                                file_id: 0,
                                start_pos: Position::new(1, 11),
                                end_pos: Position::new(1, 35),
                            }
                        ),
                        Argument::new(
                            "i",
                            Type::Unresolved(UnresolvedType::new(
                                Name {
                                    value: "i64".to_string(),
                                    span: Span {
                                        file_id: 0,
                                        start_pos: Position::new(1, 40),
                                        end_pos: Position::new(1, 43)
                                    },
                                },
                                Span {
                                    file_id: 0,
                                    start_pos: Position::new(1, 40),
                                    end_pos: Position::new(1, 43)
                                }
                            )),
                            false,
                            Span {
                                file_id: 0,
                                start_pos: Position::new(1, 37),
                                end_pos: Position::new(1, 43)
                            }
                        )
                    ],
                    Some(Type::Function(Box::new(FunctionSignature::new_anon(
                        vec![Argument::new(
                            "",
                            Type::Unresolved(UnresolvedType::new(
                                Name {
                                    value: "bool".to_string(),
                                    span: Span {
                                        file_id: 0,
                                        start_pos: Position::new(1, 52),
                                        end_pos: Position::new(1, 56)
                                    },
                                },
                                Span {
                                    file_id: 0,
                                    start_pos: Position::new(1, 52),
                                    end_pos: Position::new(1, 56)
                                }
                            )),
                            false,
                            Span {
                                file_id: 0,
                                start_pos: Position::new(1, 52),
                                end_pos: Position::new(1, 56)
                            }
                        )],
                        Some(Type::Unresolved(UnresolvedType::new(
                            Name {
                                value: "str".to_string(),
                                span: Span {
                                    file_id: 0,
                                    start_pos: Position::new(1, 61),
                                    end_pos: Position::new(1, 64)
                                },
                            },
                            Span {
                                file_id: 0,
                                start_pos: Position::new(1, 61),
                                end_pos: Position::new(1, 64)
                            }
                        ))),
                        Span {
                            file_id: 0,
                            start_pos: Position::new(1, 48),
                            end_pos: Position::new(1, 64),
                        }
                    )))),
                    Span {
                        file_id: 0,
                        start_pos: Position::new(1, 1),
                        end_pos: Position::new(1, 64),
                    }
                ),
                Closure::new(
                    vec![],
                    Span {
                        file_id: 0,
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
        let mut parser = new_parser(r#"do_thing("one", "two", true)"#);
        let result = parse_expr(&mut parser).expect("should not error");
        assert_eq!(
            result,
            Expression::FunctionCall(Box::new(FnCall::new(
                Expression::Symbol(Symbol::new(
                    Name {
                        value: "do_thing".to_string(),
                        span: Span {
                            file_id: 0,
                            start_pos: Position::new(1, 1),
                            end_pos: Position::new(1, 9),
                        },
                    },
                    Span {
                        file_id: 0,
                        start_pos: Position::new(1, 1),
                        end_pos: Position::new(1, 9),
                    },
                )),
                vec![
                    Expression::StrLiteral(StrLit {
                        value: "one".to_string(),
                        span: Span {
                            file_id: 0,
                            start_pos: Position::new(1, 10),
                            end_pos: Position::new(1, 15),
                        }
                    }),
                    Expression::StrLiteral(StrLit {
                        value: "two".to_string(),
                        span: Span {
                            file_id: 0,
                            start_pos: Position::new(1, 17),
                            end_pos: Position::new(1, 22),
                        }
                    }),
                    Expression::BoolLiteral(BoolLit {
                        value: true,
                        span: Span {
                            file_id: 0,
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
        let mut parser = new_parser(r#"let i = call(,,)"#);
        let result = Statement::parse(&mut parser);
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::ExpectedExpr,
                message: _,
                token: Some(Token {
                    kind: TokenKind::Comma,
                    span: Span {
                        file_id: 0,
                        start_pos: Position { line: 1, col: 14 },
                        end_pos: Position { line: 1, col: 15 },
                    }
                }),
                span: Span {
                    file_id: 0,
                    start_pos: Position { line: 1, col: 14 },
                    end_pos: Position { line: 1, col: 15 },
                }
            })
        ));
    }

    #[test]
    fn invalid_extra_close_paren() {
        let mut parser = new_parser(r#"{ let i = call()) }"#);
        let result = Closure::parse(&mut parser);
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::ExpectedExpr,
                message: _,
                token: Some(Token {
                    kind: TokenKind::RightParen,
                    span: Span {
                        file_id: 0,
                        start_pos: Position { line: 1, col: 17 },
                        end_pos: Position { line: 1, col: 18 },
                    }
                }),
                span: Span {
                    file_id: 0,
                    start_pos: Position { line: 1, col: 17 },
                    end_pos: Position { line: 1, col: 18 },
                }
            })
        ));
    }

    #[test]
    fn invalid_missing_close_paren() {
        let mut parser = new_parser(r#"do(((x+3) > 2) || other"#);
        let result = parse_expr(&mut parser);
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
        let mut parser = new_parser(r#"do(&& true)"#);
        let result = parse_expr(&mut parser);
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::ExpectedBeginExpr,
                message: _,
                token: Some(Token {
                    kind: TokenKind::LogicalAnd,
                    span: Span {
                        file_id: 0,
                        start_pos: Position { line: 1, col: 4 },
                        end_pos: Position { line: 1, col: 6 },
                    }
                }),
                span: Span {
                    file_id: 0,
                    start_pos: Position { line: 1, col: 4 },
                    end_pos: Position { line: 1, col: 6 },
                }
            })
        ));
    }

    #[test]
    fn empty_fn_return() {
        let code = "fn my_func(s: str) {
            if s == \"dog\" {
                return
            }

            print(\"not dog\")
        }";
        let mut parser = new_parser(code);
        let result = Function::parse(&mut parser).expect("should not error");
        assert_eq!(
            result,
            Function::new(
                FunctionSignature::new(
                    Name {
                        value: "my_func".to_string(),
                        span: Span {
                            file_id: 0,
                            start_pos: Position::new(1, 4),
                            end_pos: Position::new(1, 11)
                        }
                    },
                    vec![Argument::new(
                        "s",
                        Type::Unresolved(UnresolvedType::new(
                            Name {
                                value: "str".to_string(),
                                span: Span {
                                    file_id: 0,
                                    start_pos: Position::new(1, 15),
                                    end_pos: Position::new(1, 18)
                                },
                            },
                            Span {
                                file_id: 0,
                                start_pos: Position::new(1, 15),
                                end_pos: Position::new(1, 18)
                            }
                        )),
                        false,
                        Span {
                            file_id: 0,
                            start_pos: Position::new(1, 12),
                            end_pos: Position::new(1, 18)
                        }
                    )],
                    None,
                    Span {
                        file_id: 0,
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
                                    name: Name {
                                        value: "s".to_string(),
                                        span: Span {
                                            file_id: 0,
                                            start_pos: Position::new(2, 16),
                                            end_pos: Position::new(2, 17),
                                        },
                                    },
                                    params: vec![],
                                    span: Span {
                                        file_id: 0,
                                        start_pos: Position::new(2, 16),
                                        end_pos: Position::new(2, 17),
                                    },
                                })),
                                Operator::EqualTo,
                                Box::new(Expression::StrLiteral(StrLit {
                                    value: "dog".to_string(),
                                    span: Span {
                                        file_id: 0,
                                        start_pos: Position::new(2, 21),
                                        end_pos: Position::new(2, 26),
                                    }
                                })),
                            )),
                            Closure::new(
                                vec![Statement::Return(Ret::new(
                                    None,
                                    Span {
                                        file_id: 0,
                                        start_pos: Position::new(3, 17),
                                        end_pos: Position::new(3, 23)
                                    },
                                ))],
                                Span {
                                    file_id: 0,
                                    start_pos: Position::new(2, 27),
                                    end_pos: Position::new(4, 14)
                                },
                            ),
                            Span {
                                file_id: 0,
                                start_pos: Position::new(2, 16),
                                end_pos: Position::new(4, 14),
                            }
                        )])),
                        Statement::FunctionCall(FnCall::new(
                            Expression::Symbol(Symbol::new(
                                Name {
                                    value: "print".to_string(),
                                    span: Span {
                                        file_id: 0,
                                        start_pos: Position::new(6, 13),
                                        end_pos: Position::new(6, 18)
                                    },
                                },
                                Span {
                                    file_id: 0,
                                    start_pos: Position::new(6, 13),
                                    end_pos: Position::new(6, 18)
                                },
                            )),
                            vec![Expression::StrLiteral(StrLit {
                                value: "not dog".to_string(),
                                span: Span {
                                    file_id: 0,
                                    start_pos: Position::new(6, 19),
                                    end_pos: Position::new(6, 28),
                                }
                            })],
                            Position::new(6, 29),
                        ))
                    ],
                    Span {
                        file_id: 0,
                        start_pos: Position::new(1, 20),
                        end_pos: Position::new(7, 10),
                    },
                ),
                false
            )
        );
    }

    #[test]
    fn missing_fn_closing_brace() {
        let code = r#"fn thing() -> i64 {
            return 4 / 2 + 8
        "#;
        let mut parser = new_parser(code);
        let result = Function::parse(&mut parser);
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
        let mut parser = new_parser("let thing: i64 = 234");
        Statement::parse(&mut parser).expect("should not error");
    }

    #[test]
    fn invalid_type_cast() {
        let code = r#"
            fn main() {
                let a = 5u64
                let b = a as 543
            }
        "#;
        let mut parser = new_parser(code);
        let result = Function::parse(&mut parser);
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
            {
                let a = thing
                (thing) = 2
            }
        "#;
        let mut parser = new_parser(raw);
        let result = Closure::parse(&mut parser);
        assert_eq!(
            result.unwrap().statements,
            vec![
                Statement::VariableDeclaration(VariableDeclaration {
                    maybe_type: None,
                    is_mut: false,
                    name: Name {
                        value: "a".to_string(),
                        span: Span {
                            file_id: 0,
                            start_pos: Position::new(3, 21),
                            end_pos: Position::new(3, 22),
                        },
                    },
                    value: Expression::Symbol(Symbol {
                        maybe_mod_name: None,
                        name: Name {
                            value: "thing".to_string(),
                            span: Span {
                                file_id: 0,
                                start_pos: Position::new(3, 25),
                                end_pos: Position::new(3, 30),
                            },
                        },
                        params: vec![],
                        span: Span {
                            file_id: 0,
                            start_pos: Position::new(3, 25),
                            end_pos: Position::new(3, 30),
                        }
                    }),
                    span: Span {
                        file_id: 0,
                        start_pos: Position::new(3, 17),
                        end_pos: Position::new(3, 30),
                    },
                }),
                Statement::VariableAssignment(VariableAssignment::new(
                    Expression::Symbol(Symbol {
                        maybe_mod_name: None,
                        name: Name {
                            value: "thing".to_string(),
                            span: Span {
                                file_id: 0,
                                start_pos: Position::new(4, 18),
                                end_pos: Position::new(4, 23),
                            },
                        },
                        params: vec![],
                        span: Span {
                            file_id: 0,
                            start_pos: Position::new(4, 18),
                            end_pos: Position::new(4, 23),
                        },
                    }),
                    Expression::IntLiteral(IntLit {
                        value: 2,
                        has_suffix: false,
                        span: Span {
                            file_id: 0,
                            start_pos: Position::new(4, 27),
                            end_pos: Position::new(4, 28),
                        }
                    }),
                    Position::new(4, 17),
                ))
            ]
        )
    }

    #[test]
    fn invalid_mod_paths() {
        for path in ["/thing", "../thing", "path/../table"] {
            let raw = format!(
                r#"
                    mod test

                    use "{path}" @thing
                "#
            );
            let tokens = lex(raw.as_str(), 0).expect("should succeed");
            let mut parser = FileParser::new(0, Stream::new(tokens));
            let result = SrcFile::parse(&mut parser);
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
