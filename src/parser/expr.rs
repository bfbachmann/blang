use std::collections::VecDeque;
use std::fmt;

use crate::lexer::kind::TokenKind;
use crate::lexer::pos::{Locatable, Position};
use crate::lexer::token::Token;
use crate::parser::bool_lit::BoolLit;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::func::Function;
use crate::parser::func_call::FunctionCall;
use crate::parser::i64_lit::I64Lit;
use crate::parser::op::Operator;
use crate::parser::program::Program;
use crate::parser::r#struct::StructInit;
use crate::parser::string_lit::StringLit;
use crate::parser::var_ref::VarRef;
use crate::parser::ParseResult;

#[derive(Debug)]
enum OutputNode {
    Operator(Operator),
    BasicExpr(Expression),
}

impl OutputNode {
    fn from_op(op: Operator) -> Self {
        OutputNode::Operator(op)
    }

    fn from_basic_expr(expr: Expression) -> Self {
        OutputNode::BasicExpr(expr)
    }
}

/// Represents basic and composite expressions. A basic expression can be any of the following:
///  - an identifier representing a variable value
///  - a literal value
///  - a function call
///  - a unary operator followed by a composite expression (`<unary_op> <comp_expr>`)
/// whereas a composite expression can be any token sequence of the forms
///
///     <basic_expr> <binary_op> <comp_expr>
///
/// where
///  - `basic_expr` is a basic expression
///  - `binary_op` is a binary operator
///  - `comp_expr` is a composite expression
#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    // Basic expressions.
    VariableReference(VarRef),
    BoolLiteral(BoolLit),
    I64Literal(I64Lit),
    StringLiteral(StringLit),
    FunctionCall(FunctionCall),
    AnonFunction(Box<Function>),
    UnaryOperation(Operator, Box<Expression>),
    StructInit(StructInit),

    // Composite expressions.
    BinaryOperation(Box<Expression>, Operator, Box<Expression>),
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::VariableReference(s) => write!(f, "{}", s),
            Expression::BoolLiteral(b) => write!(f, "{}", b),
            Expression::I64Literal(i) => write!(f, "{}", i),
            Expression::StringLiteral(s) => write!(f, "{}", s),
            Expression::FunctionCall(fn_call) => write!(f, "{}", fn_call),
            Expression::AnonFunction(func) => write!(f, "{}", func),
            Expression::UnaryOperation(op, expr) => write!(f, "{}{}", op, expr),
            Expression::BinaryOperation(left_expr, op, right_expr) => {
                write!(f, "{} {} {}", left_expr, op, right_expr)
            }
            Expression::StructInit(struct_init) => {
                write!(f, "struct initialization {}", struct_init)
            }
        }
    }
}

impl Locatable for Expression {
    fn start_pos(&self) -> &Position {
        match self {
            Expression::VariableReference(var_ref) => var_ref.start_pos(),
            Expression::BoolLiteral(bool_lit) => bool_lit.start_pos(),
            Expression::I64Literal(i64_lit) => i64_lit.start_pos(),
            Expression::StringLiteral(string_lit) => string_lit.start_pos(),
            Expression::FunctionCall(fn_call) => fn_call.start_pos(),
            Expression::AnonFunction(func) => func.start_pos(),
            Expression::UnaryOperation(_, expr) => expr.start_pos(),
            Expression::StructInit(struct_init) => struct_init.start_pos(),
            Expression::BinaryOperation(left, _, _) => left.start_pos(),
        }
    }

    fn end_pos(&self) -> &Position {
        match self {
            Expression::VariableReference(var_ref) => var_ref.end_pos(),
            Expression::BoolLiteral(bool_lit) => bool_lit.end_pos(),
            Expression::I64Literal(i64_lit) => i64_lit.end_pos(),
            Expression::StringLiteral(string_lit) => string_lit.end_pos(),
            Expression::FunctionCall(fn_call) => fn_call.end_pos(),
            Expression::AnonFunction(func) => func.end_pos(),
            Expression::UnaryOperation(_, expr) => expr.end_pos(),
            Expression::StructInit(struct_init) => struct_init.end_pos(),
            Expression::BinaryOperation(left, _, _) => left.end_pos(),
        }
    }
}

impl Expression {
    /// Parses an expression tree from reverse Polish notation.
    fn from_rpn(q: &mut VecDeque<OutputNode>) -> ParseResult<Self> {
        match q.pop_back() {
            // If the node is an operator, we need to assemble its children.
            Some(OutputNode::Operator(op)) => {
                let right_child = Expression::from_rpn(q)?;
                let left_child = Expression::from_rpn(q)?;
                Ok(Expression::BinaryOperation(
                    Box::new(left_child),
                    op,
                    Box::new(right_child),
                ))
            }
            // Otherwise, this is a leaf node (i.e. basic expression).
            Some(OutputNode::BasicExpr(expr)) => Ok(expr),
            // The queue should not be empty. If this happens, it means that the queue passed to
            // this function was not valid RPN.
            None => Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "unexpected end of expression",
                None,
                Position::default(),
                Position::default(),
            )),
        }
    }

    /// Parses a basic expression. A basic expression can be any of the following:
    ///  - an identifier representing a variable value
    ///  - a literal value (includes anonymous functions)
    ///  - a function call
    ///  - a unary operator followed by a composite expression (`<unary_op> <comp_expr>`)
    ///  - a struct initialization (see `StructInit::from`)
    fn from_basic(
        tokens: &mut VecDeque<Token>,
        is_arg: bool,
        is_cond: bool,
    ) -> ParseResult<Option<Expression>> {
        match tokens.pop_front() {
            // If the first token is "fn", we'll assume the expression is an anonymous function.
            Some(
                token @ Token {
                    kind: TokenKind::Function,
                    ..
                },
            ) => {
                // Put the "fn" token back because it's expected by Function::from_anon.
                tokens.push_front(token);

                // Parse the anonymous function and return it.
                let func = Function::from_anon(tokens)?;
                Ok(Some(Expression::AnonFunction(Box::new(func))))
            }

            // If the first token is "struct", it's an inline struct initialization.
            Some(
                token @ Token {
                    kind: TokenKind::Struct,
                    ..
                },
            ) => {
                tokens.push_front(token);
                let struct_init = StructInit::from(tokens)?;
                Ok(Some(Expression::StructInit(struct_init)))
            }

            // If the first token is an identifier, the expression can be a function call,
            // a variable value, or a struct initialization.
            Some(
                token @ Token {
                    kind: TokenKind::Identifier(_),
                    ..
                },
            ) => {
                match tokens.front() {
                    // If the token is "(", it's a function call.
                    Some(&Token {
                        kind: TokenKind::LeftParen,
                        ..
                    }) => {
                        tokens.push_front(token);
                        let call = FunctionCall::from(tokens)?;
                        Ok(Some(Expression::FunctionCall(call)))
                    }

                    // If the token is "{", try parse the expression as struct initialization. If
                    // it's not valid struct initialization, we'll assume it's a variable value.
                    Some(&Token {
                        kind: TokenKind::BeginClosure,
                        ..
                    }) => {
                        // If we're in a conditional, we can safely assume that this is a variable
                        // reference. Otherwise, it is struct initialization.
                        tokens.push_front(token);
                        if is_cond {
                            let var_ref = VarRef::from(tokens)?;
                            Ok(Some(Expression::VariableReference(var_ref)))
                        } else {
                            let struct_init = StructInit::from(tokens)?;
                            Ok(Some(Expression::StructInit(struct_init)))
                        }
                    }

                    // If the next token is anything else, we'll assume it's a variable value.
                    _ => {
                        tokens.push_front(token);
                        let var_ref = VarRef::from(tokens)?;
                        Ok(Some(Expression::VariableReference(var_ref)))
                    }
                }
            }

            // If the first token is a unary operator, we know the rest should be a composite
            // expression.
            Some(
                token @ Token {
                    kind: TokenKind::Not,
                    ..
                },
            ) => {
                let op = Operator::from(&token.kind).unwrap();
                let expr = Expression::from(tokens, is_arg, is_cond)?;
                Ok(Some(Expression::UnaryOperation(op, Box::new(expr))))
            }

            // Check if it's a bool literal.
            Some(
                token @ Token {
                    kind: TokenKind::BoolLiteral(_),
                    ..
                },
            ) => {
                tokens.push_front(token);
                let bool_lit = BoolLit::from(tokens)?;
                Ok(Some(Expression::BoolLiteral(bool_lit)))
            }

            // Check if it's an integer literal.
            Some(
                token @ Token {
                    kind: TokenKind::I64Literal(_),
                    ..
                },
            ) => {
                tokens.push_front(token);
                let i64_lit = I64Lit::from(tokens)?;
                Ok(Some(Expression::I64Literal(i64_lit)))
            }

            // Check if it's a string literal.
            Some(
                token @ Token {
                    kind: TokenKind::StringLiteral(_),
                    ..
                },
            ) => {
                tokens.push_front(token);
                let string_lit = StringLit::from(tokens)?;
                Ok(Some(Expression::StringLiteral(string_lit)))
            }

            // If the token is anything else, we assume there is no basic expression here.
            Some(token) => {
                // Put the token back on the queue before returning.
                tokens.push_front(token);
                Ok(None)
            }
            None => Ok(None),
        }
    }

    /// Parses a basic or composite expression from the given tokens. A basic expression can be any
    /// of the following:
    ///  - an identifier representing a variable value
    ///  - a literal value
    ///  - a function call
    ///  - a unary operator followed by a composite expression (`<unary_op> <comp_expr>`)
    ///  - a struct initialization (see `StructInit::from`)
    /// whereas a composite expression can be any token sequence of the form
    ///
    ///     <basic_expr> <binary_op> <comp_expr>
    ///
    /// where
    ///  - `basic_expr` is a basic expression
    ///  - `binary_op` is a binary operator
    ///  - `comp_expr` is a composite expression
    ///
    /// This function implements a modified version of the shunting yard algorithm. The general
    /// structure is the same, but modifications have been made to handle negative values and
    /// function calls with arbitrary arguments.
    pub fn from(
        tokens: &mut VecDeque<Token>,
        is_arg: bool,
        is_cond: bool,
    ) -> ParseResult<Expression> {
        let start_pos = Program::current_position(tokens);
        let mut out_q: VecDeque<OutputNode> = VecDeque::new();
        let mut op_stack: VecDeque<Token> = VecDeque::new();
        let mut last_token: Option<Token> = None;
        let mut expect_binop_or_end = false;

        // While there are still tokens to be read, pop and process them one by one in order to
        // form an output queue of expressions in reverse Polish notation.
        'outer: while let Some(op1_token) = tokens.pop_front() {
            // If the token is ",", we can stop trying to parse the expression and assume we've
            // reached the end because commas aren't valid in expressions.
            if let Token {
                kind: TokenKind::Comma,
                ..
            } = op1_token
            {
                // Add the "," back to the token sequence because it's expected during
                // function argument parsing.
                tokens.push_front(op1_token);
                break;
            }
            // Check if the token is "(".
            else if let Some(Operator::LeftParen) = Operator::from(&op1_token.kind) {
                // We should not be here if we we're expecting a binary operator or the end of the
                // expression.
                if expect_binop_or_end {
                    return Err(ParseError::new_with_token(
                        ErrorKind::ExpectedBinOpOrEndOfExpr,
                        "expected binary operator or end of expression",
                        op1_token,
                    ));
                }

                op_stack.push_back(op1_token.clone());
            }
            // Check if the token is ")".
            else if let Some(Operator::RightParen) = Operator::from(&op1_token.kind) {
                // Look for the "(" that matches this ")" on the operator stack.
                loop {
                    match op_stack.back() {
                        // If the operator at the top of the operator stack is "(", we're done.
                        Some(&Token {
                            kind: TokenKind::LeftParen,
                            ..
                        }) => {
                            break;
                        }
                        // If there is no operator at the top of the stack, then this is an
                        // unmatched closing parenthesis. We'll allow this because it will happen
                        // in the case where the current expression is the last argument in a
                        // function call.
                        None => {
                            if is_arg {
                                // Add the ")" back to the token sequence because it's expected during
                                // function argument parsing.
                                tokens.push_front(op1_token);
                                break 'outer;
                            }

                            return Err(ParseError::new_with_token(
                                ErrorKind::UnmatchedCloseParen,
                                "unmatched closing parenthesis in expression",
                                op1_token,
                            ));
                        }
                        // Otherwise, we just pop the operator from the stack and add it to the
                        // output queue.
                        _ => {
                            // Pop op2 from the operator stack and onto the output queue.
                            let op2 = Operator::from(&op_stack.pop_back().unwrap().kind).unwrap();
                            out_q.push_back(OutputNode::from_op(op2));
                        }
                    }
                }

                // Assert there is a "(" at the top of the operator stack.
                if let Some(&Token {
                    kind: TokenKind::LeftParen,
                    ..
                }) = op_stack.back()
                {
                    // Pop the "(" from the operator stack and discard it
                    op_stack.pop_back();
                } else {
                    return Err(ParseError::new_with_token(
                        ErrorKind::UnmatchedCloseParen,
                        "unmatched closing parenthesis in expression",
                        op1_token,
                    ));
                }
            }
            // Check if the token is a unary operator.
            else if let Some(Operator::Not) = Operator::from(&op1_token.kind) {
                // We should not be here if we we're expecting a binary operator or the end of the
                // expression.
                if expect_binop_or_end {
                    return Err(ParseError::new_with_token(
                        ErrorKind::ExpectedBinOpOrEndOfExpr,
                        "expected binary operator or end of expression",
                        op1_token,
                    ));
                }

                // Add the operator back to the token deque so it can be parsed as part of the basic
                // expression.
                tokens.push_front(op1_token.clone());
                let expr = Expression::from_basic(tokens, is_arg, is_cond)?;
                out_q.push_back(OutputNode::from_basic_expr(expr.unwrap()));
                expect_binop_or_end = true
            }
            // Check if the token is a binary operator.
            else if let Some(op1) = Operator::from(&op1_token.kind) {
                // At this point, we know we have a binary operator. We should error here if we're
                // not expecting a binary operator unless it's a negative.
                if expect_binop_or_end {
                    expect_binop_or_end = false;

                    while let Some(&ref op2_token) = op_stack.back() {
                        let op2 = Operator::from(&op2_token.kind).unwrap();
                        if op2 != Operator::LeftParen
                            && (op2.precedence() > op1.precedence()
                                || (op2.precedence() == op1.precedence()
                                    && op1.is_left_associative()))
                        {
                            // Pop op2 from the operator stack and onto the output queue.
                            let op2 = Operator::from(&op_stack.pop_back().unwrap().kind).unwrap();
                            out_q.push_back(OutputNode::from_op(op2));
                        } else {
                            break;
                        }
                    }

                    // Push operator 1 onto the operator stack.
                    op_stack.push_back(op1_token.clone());
                } else if op1 == Operator::Subtract {
                    // Error if this is a double negative. We could actually handle this cleanly,
                    // by why allow confusing and unnecessary syntax?
                    if let Some(
                        token @ Token {
                            kind: TokenKind::Subtract,
                            ..
                        },
                    ) = last_token.clone()
                    {
                        return Err(ParseError::new(
                            ErrorKind::UseOfDoubleNegative,
                            "use of double negative in expression",
                            Some(token),
                            start_pos,
                            op1_token.end.clone(),
                        ));
                    }

                    // We have a negative value here, so we're going to represent it as the value
                    // multiplied by -1. Push -1 to the output queue and push * to the operator
                    // stack.
                    out_q.push_back(OutputNode::from_basic_expr(Expression::I64Literal(
                        I64Lit::new_with_default_pos(-1),
                    )));
                    op_stack.push_back(Token::new(TokenKind::Multiply, 0, 0, 0));
                } else {
                    return Err(ParseError::new_with_token(
                        ErrorKind::UnexpectedOperator,
                        "unexpected operator",
                        op1_token,
                    ));
                }
            }
            // At this point we know that the token is not an operator or a parenthesis.
            else {
                // If we're expecting a binary operator or the end of the expression and we've
                // reached this point, we'll assume that means we've reached the end of the
                // expression.
                if expect_binop_or_end {
                    tokens.push_front(op1_token);
                    break;
                }

                // If the last token was a binary operator or this is the beginning of the
                // expression, then we can expect what follows to be a basic expression. Otherwise,
                // we should error.
                match last_token {
                    None => {
                        // This is the beginning of the expression, so we expect a basic expression.
                        tokens.push_front(op1_token.clone());
                        if let Some(expr) = Expression::from_basic(tokens, is_arg, is_cond)? {
                            out_q.push_back(OutputNode::from_basic_expr(expr));
                            expect_binop_or_end = true;
                        } else {
                            return Err(ParseError::new_with_token(
                                ErrorKind::ExpectedBeginExpr,
                                format!(
                                    "expected beginning of expression, but found {}",
                                    op1_token
                                )
                                .as_str(),
                                op1_token,
                            ));
                        }
                    }
                    Some(last) => {
                        // This is the continuation of the expression, so if the last token was a
                        // binary operator, we expect a basic expression - it can't be composite
                        // because that would have been handled by other branches in the if
                        // statement above.
                        if let Some(last_op) = Operator::from(&last.kind) {
                            if last_op.is_binary() {
                                tokens.push_front(op1_token.clone());
                                if let Some(expr) = Expression::from_basic(tokens, is_arg, is_cond)?
                                {
                                    out_q.push_back(OutputNode::from_basic_expr(expr));
                                    expect_binop_or_end = true;
                                } else {
                                    return Err(ParseError::new_with_token(
                                        ErrorKind::ExpectedBasicExpr,
                                        format!(
                                            "expected basic expression, but found {}",
                                            op1_token
                                        )
                                        .as_str(),
                                        op1_token,
                                    ));
                                }
                            } else {
                                return Err(ParseError::new_with_token(
                                    ErrorKind::ExpectedExpr,
                                    format!("expected expression, but found {}", op1_token)
                                        .as_str(),
                                    op1_token,
                                ));
                            }
                        } else {
                            // At this point we know we the token is not part of the expression, so
                            // we're done.
                            tokens.push_front(op1_token);
                            break;
                        }
                    }
                };
            }

            last_token = Some(op1_token);
        }

        // Pop the remaining items from the operator stack into the output queue.
        while let Some(op) = op_stack.pop_back() {
            // Assert the operator on top of the stack is not "(".
            if let token @ Token {
                kind: TokenKind::LeftParen,
                start: _,
                end,
            } = op
            {
                return Err(ParseError::new(
                    ErrorKind::UnmatchedOpenParen,
                    "unmatched opening parenthesis in expression",
                    Some(token),
                    start_pos,
                    end,
                ));
            }

            // Pop the operator from the operator stack onto the output queue.
            let op = Operator::from(&op.kind).unwrap();
            out_q.push_back(OutputNode::from_op(op));
        }

        // At this point we have an output queue representing the tokens in the expression in
        // reverse Polish notation (RPN). We just have to convert the RPN into an expression tree.
        Ok(Expression::from_rpn(&mut out_q)?)
    }
}

#[cfg(test)]
mod tests {
    use std::io::{BufRead, Cursor};

    use crate::lexer::kind::TokenKind;
    use crate::lexer::pos::Position;
    use crate::lexer::token::Token;
    use crate::parser::bool_lit::BoolLit;
    use crate::parser::error::{ErrorKind, ParseError};
    use crate::parser::expr::Expression;
    use crate::parser::func_call::FunctionCall;
    use crate::parser::i64_lit::I64Lit;
    use crate::parser::op::Operator;
    use crate::parser::string_lit::StringLit;
    use crate::parser::var_ref::VarRef;

    fn parse(raw: &str) -> Expression {
        let mut tokens = Token::tokenize(Cursor::new(raw).lines()).expect("should not error");
        Expression::from(&mut tokens, false, false).expect("should not error")
    }

    #[test]
    fn parse_basic_var_value() {
        assert_eq!(
            parse(r#"my_var"#),
            Expression::VariableReference(VarRef {
                var_name: "my_var".to_string(),
                start_pos: Position::new(1, 1),
                end_pos: Position::new(1, 7),
            })
        );
    }

    #[test]
    fn parse_basic_bool_literal() {
        assert_eq!(
            parse("true"),
            Expression::BoolLiteral(BoolLit::new(true, Position::new(1, 1), Position::new(1, 5)))
        );
        assert_eq!(
            parse("false"),
            Expression::BoolLiteral(BoolLit::new(
                false,
                Position::new(1, 1),
                Position::new(1, 6)
            ))
        );
    }

    #[test]
    fn parse_basic_i64_literal() {
        assert_eq!(
            parse("123"),
            Expression::I64Literal(I64Lit {
                value: 123,
                start_pos: Position::new(1, 1),
                end_pos: Position::new(1, 4),
            })
        );
    }

    #[test]
    fn parse_basic_string_literal() {
        assert_eq!(
            parse(r#""this is my \"String\"""#),
            Expression::StringLiteral(StringLit {
                value: r#"this is my "String""#.to_string(),
                start_pos: Position::new(1, 1),
                end_pos: Position::new(1, 24),
            })
        );
    }

    #[test]
    fn parse_function_call() {
        assert_eq!(
            parse("call(3 * 2 - 2, other(!thing, 1 > var % 2))"),
            Expression::FunctionCall(FunctionCall::new(
                "call",
                vec![
                    Expression::BinaryOperation(
                        Box::new(Expression::BinaryOperation(
                            Box::new(Expression::I64Literal(I64Lit {
                                value: 3,
                                start_pos: Position::new(1, 6),
                                end_pos: Position::new(1, 7),
                            })),
                            Operator::Multiply,
                            Box::new(Expression::I64Literal(I64Lit {
                                value: 2,
                                start_pos: Position::new(1, 10),
                                end_pos: Position::new(1, 11),
                            }))
                        )),
                        Operator::Subtract,
                        Box::new(Expression::I64Literal(I64Lit {
                            value: 2,
                            start_pos: Position::new(1, 14),
                            end_pos: Position::new(1, 15),
                        }))
                    ),
                    Expression::FunctionCall(FunctionCall::new(
                        "other",
                        vec![
                            Expression::UnaryOperation(
                                Operator::Not,
                                Box::new(Expression::VariableReference(VarRef {
                                    var_name: "thing".to_string(),
                                    start_pos: Position::new(1, 24),
                                    end_pos: Position::new(1, 29),
                                }))
                            ),
                            Expression::BinaryOperation(
                                Box::new(Expression::I64Literal(I64Lit {
                                    value: 1,
                                    start_pos: Position::new(1, 31),
                                    end_pos: Position::new(1, 32),
                                })),
                                Operator::GreaterThan,
                                Box::new(Expression::BinaryOperation(
                                    Box::new(Expression::VariableReference(VarRef {
                                        var_name: "var".to_string(),
                                        start_pos: Position::new(1, 35),
                                        end_pos: Position::new(1, 38),
                                    })),
                                    Operator::Modulo,
                                    Box::new(Expression::I64Literal(I64Lit {
                                        value: 2,
                                        start_pos: Position::new(1, 41),
                                        end_pos: Position::new(1, 42),
                                    }))
                                ))
                            )
                        ],
                        Position::new(1, 17),
                        Position::new(1, 43)
                    ))
                ],
                Position::new(1, 1),
                Position::new(1, 44),
            ))
        );
    }

    #[test]
    fn parse_i64_arithmetic() {
        assert_eq!(
            parse("(3 + 6) / 3 - 5 + 298 * 3"),
            Expression::BinaryOperation(
                Box::new(Expression::BinaryOperation(
                    Box::new(Expression::BinaryOperation(
                        Box::new(Expression::BinaryOperation(
                            Box::new(Expression::I64Literal(I64Lit {
                                value: 3,
                                start_pos: Position::new(1, 2),
                                end_pos: Position::new(1, 3),
                            })),
                            Operator::Add,
                            Box::new(Expression::I64Literal(I64Lit {
                                value: 6,
                                start_pos: Position::new(1, 6),
                                end_pos: Position::new(1, 7),
                            }))
                        )),
                        Operator::Divide,
                        Box::new(Expression::I64Literal(I64Lit {
                            value: 3,
                            start_pos: Position::new(1, 11),
                            end_pos: Position::new(1, 12),
                        }))
                    )),
                    Operator::Subtract,
                    Box::new(Expression::I64Literal(I64Lit {
                        value: 5,
                        start_pos: Position::new(1, 15),
                        end_pos: Position::new(1, 16),
                    }))
                )),
                Operator::Add,
                Box::new(Expression::BinaryOperation(
                    Box::new(Expression::I64Literal(I64Lit {
                        value: 298,
                        start_pos: Position::new(1, 19),
                        end_pos: Position::new(1, 22),
                    })),
                    Operator::Multiply,
                    Box::new(Expression::I64Literal(I64Lit {
                        value: 3,
                        start_pos: Position::new(1, 25),
                        end_pos: Position::new(1, 26),
                    }))
                ))
            )
        )
    }

    #[test]
    fn parse_multiline() {
        let raw = "(var - 3) / 4 * \n(call(true) % 2) + \n5";
        assert_eq!(
            parse(raw),
            Expression::BinaryOperation(
                Box::new(Expression::BinaryOperation(
                    Box::new(Expression::BinaryOperation(
                        Box::new(Expression::BinaryOperation(
                            Box::new(Expression::VariableReference(VarRef {
                                var_name: "var".to_string(),
                                start_pos: Position::new(1, 2),
                                end_pos: Position::new(1, 5),
                            })),
                            Operator::Subtract,
                            Box::new(Expression::I64Literal(I64Lit {
                                value: 3,
                                start_pos: Position::new(1, 8),
                                end_pos: Position::new(1, 9)
                            })),
                        )),
                        Operator::Divide,
                        Box::new(Expression::I64Literal(I64Lit {
                            value: 4,
                            start_pos: Position::new(1, 13),
                            end_pos: Position::new(1, 14)
                        })),
                    )),
                    Operator::Multiply,
                    Box::new(Expression::BinaryOperation(
                        Box::new(Expression::FunctionCall(FunctionCall::new(
                            "call",
                            vec![Expression::BoolLiteral(BoolLit {
                                value: true,
                                start_pos: Position::new(2, 7),
                                end_pos: Position::new(2, 11)
                            })],
                            Position::new(2, 2),
                            Position::new(2, 12)
                        ))),
                        Operator::Modulo,
                        Box::new(Expression::I64Literal(I64Lit {
                            value: 2,
                            start_pos: Position::new(2, 15),
                            end_pos: Position::new(2, 16)
                        })),
                    )),
                )),
                Operator::Add,
                Box::new(Expression::I64Literal(I64Lit {
                    value: 5,
                    start_pos: Position::new(3, 1),
                    end_pos: Position::new(3, 2)
                })),
            )
        );
    }

    #[test]
    fn parse_unmatched_open_paren() {
        let mut tokens =
            Token::tokenize(Cursor::new("3 - 4 / (2 * 3:").lines()).expect("should not error");
        let result = Expression::from(&mut tokens, false, false);
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::UnmatchedOpenParen,
                message: _,
                token: Some(Token {
                    kind: TokenKind::LeftParen,
                    start: Position { line: 1, col: 9 },
                    end: Position { line: 1, col: 10 },
                }),
                start_pos: Position { line: 1, col: 1 },
                end_pos: Position { line: 1, col: 10 },
            })
        ));
    }

    #[test]
    fn parse_composite_negative_values() {
        let mut tokens = Token::tokenize(Cursor::new("-8 - (-100 + 2) * 4 / 2 + 8").lines())
            .expect("should not error");
        let result = Expression::from(&mut tokens, false, false).expect("should not error");
        assert_eq!(
            result,
            Expression::BinaryOperation(
                Box::new(Expression::BinaryOperation(
                    Box::new(Expression::BinaryOperation(
                        Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(-1))),
                        Operator::Multiply,
                        Box::new(Expression::I64Literal(I64Lit {
                            value: 8,
                            start_pos: Position::new(1, 2),
                            end_pos: Position::new(1, 3),
                        })),
                    )),
                    Operator::Subtract,
                    Box::new(Expression::BinaryOperation(
                        Box::new(Expression::BinaryOperation(
                            Box::new(Expression::BinaryOperation(
                                Box::new(Expression::BinaryOperation(
                                    Box::new(Expression::I64Literal(I64Lit {
                                        value: -1,
                                        start_pos: Position::default(),
                                        end_pos: Position::default(),
                                    })),
                                    Operator::Multiply,
                                    Box::new(Expression::I64Literal(I64Lit {
                                        value: 100,
                                        start_pos: Position::new(1, 8),
                                        end_pos: Position::new(1, 11),
                                    }))
                                )),
                                Operator::Add,
                                Box::new(Expression::I64Literal(I64Lit {
                                    value: 2,
                                    start_pos: Position::new(1, 14),
                                    end_pos: Position::new(1, 15)
                                })),
                            )),
                            Operator::Multiply,
                            Box::new(Expression::I64Literal(I64Lit {
                                value: 4,
                                start_pos: Position::new(1, 19),
                                end_pos: Position::new(1, 20)
                            })),
                        )),
                        Operator::Divide,
                        Box::new(Expression::I64Literal(I64Lit {
                            value: 2,
                            start_pos: Position::new(1, 23),
                            end_pos: Position::new(1, 24)
                        })),
                    )),
                )),
                Operator::Add,
                Box::new(Expression::I64Literal(I64Lit {
                    value: 8,
                    start_pos: Position::new(1, 27),
                    end_pos: Position::new(1, 28)
                })),
            )
        );
    }

    #[test]
    fn parse_basic_negative_values() {
        let mut tokens = Token::tokenize(Cursor::new("-8").lines()).expect("should not error");
        let result = Expression::from(&mut tokens, false, false).expect("should not error");
        assert_eq!(
            result,
            Expression::BinaryOperation(
                Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(-1))),
                Operator::Multiply,
                Box::new(Expression::I64Literal(I64Lit {
                    value: 8,
                    start_pos: Position::new(1, 2),
                    end_pos: Position::new(1, 3),
                })),
            )
        );

        let mut tokens = Token::tokenize(Cursor::new("-x").lines()).expect("should not error");
        let result = Expression::from(&mut tokens, false, false).expect("should not error");
        assert_eq!(
            result,
            Expression::BinaryOperation(
                Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(-1))),
                Operator::Multiply,
                Box::new(Expression::VariableReference(VarRef {
                    var_name: "x".to_string(),
                    start_pos: Position::new(1, 2),
                    end_pos: Position::new(1, 3),
                })),
            )
        );

        let mut tokens = Token::tokenize(Cursor::new("-f()").lines()).expect("should not error");
        let result = Expression::from(&mut tokens, false, false).expect("should not error");
        assert_eq!(
            result,
            Expression::BinaryOperation(
                Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(-1))),
                Operator::Multiply,
                Box::new(Expression::FunctionCall(FunctionCall::new(
                    "f",
                    vec![],
                    Position::new(1, 2),
                    Position::new(1, 5)
                ))),
            )
        );
    }

    #[test]
    fn parse_unexpected_operator() {
        let inputs = [
            "2 ++6",
            "v - 3 * (4 +*- a)",
            "**3",
            "3 **2",
            "4 / / 4",
            "%%2",
        ];

        for input in inputs {
            let mut tokens = Token::tokenize(Cursor::new(input).lines()).expect("should not error");
            let result = Expression::from(&mut tokens, false, false);
            assert!(matches!(
                result,
                Err(ParseError {
                    kind: ErrorKind::UnexpectedOperator,
                    ..
                })
            ))
        }
    }

    #[test]
    fn parse_redundant_parens() {
        let mut tokens =
            Token::tokenize(Cursor::new("(((1>0)+1))").lines()).expect("should not error");
        let result = Expression::from(&mut tokens, false, false).expect("should not error");
        assert_eq!(
            result,
            Expression::BinaryOperation(
                Box::new(Expression::BinaryOperation(
                    Box::new(Expression::I64Literal(I64Lit {
                        value: 1,
                        start_pos: Position::new(1, 4),
                        end_pos: Position::new(1, 5)
                    })),
                    Operator::GreaterThan,
                    Box::new(Expression::I64Literal(I64Lit {
                        value: 0,
                        start_pos: Position::new(1, 6),
                        end_pos: Position::new(1, 7)
                    })),
                )),
                Operator::Add,
                Box::new(Expression::I64Literal(I64Lit {
                    value: 1,
                    start_pos: Position::new(1, 9),
                    end_pos: Position::new(1, 10)
                })),
            )
        )
    }

    #[test]
    fn parse_unexpected_end_of_expr() {
        for input in ["2 -", "ok *", "5/", "v -3 + -", "(3 % 3) +"] {
            let mut tokens = Token::tokenize(Cursor::new(input).lines()).expect("should not error");
            let result = Expression::from(&mut tokens, false, false);
            assert!(matches!(
                result,
                Err(ParseError {
                    kind: ErrorKind::UnexpectedEOF,
                    ..
                })
            ))
        }
    }

    #[test]
    fn parse_repeated_minus() {
        let input = "--(-v--a)-2--(-100 -- call(1))";
        let mut tokens = Token::tokenize(Cursor::new(input).lines()).expect("should not error");
        let result = Expression::from(&mut tokens, false, false);
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::UseOfDoubleNegative,
                message: _,
                token: Some(Token {
                    kind: TokenKind::Subtract,
                    start: Position { line: 1, col: 1 },
                    end: Position { line: 1, col: 2 },
                }),
                start_pos: Position { line: 1, col: 1 },
                end_pos: Position { line: 1, col: 3 },
            })
        ))
    }

    #[test]
    fn redundant_parenthesized_negatives() {
        let input = "-(-b-(-100))";
        let mut tokens = Token::tokenize(Cursor::new(input).lines()).expect("should not error");
        let result = Expression::from(&mut tokens, false, false).expect("should not error");
        assert_eq!(
            result,
            Expression::BinaryOperation(
                Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(-1))),
                Operator::Multiply,
                Box::new(Expression::BinaryOperation(
                    Box::new(Expression::BinaryOperation(
                        Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(-1))),
                        Operator::Multiply,
                        Box::new(Expression::VariableReference(VarRef {
                            var_name: "b".to_string(),
                            start_pos: Position::new(1, 4),
                            end_pos: Position::new(1, 5),
                        })),
                    )),
                    Operator::Subtract,
                    Box::new(Expression::BinaryOperation(
                        Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(-1))),
                        Operator::Multiply,
                        Box::new(Expression::I64Literal(I64Lit {
                            value: 100,
                            start_pos: Position::new(1, 8),
                            end_pos: Position::new(1, 11),
                        })),
                    )),
                )),
            )
        )
    }
}
