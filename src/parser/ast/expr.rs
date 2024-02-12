use std::collections::{HashSet, VecDeque};
use std::fmt;
use std::fmt::{Display, Formatter};

use colored::Colorize;

use crate::lexer::pos::{Locatable, Position};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::array::ArrayInit;
use crate::parser::ast::bool_lit::BoolLit;
use crate::parser::ast::func::Function;
use crate::parser::ast::func_call::FunctionCall;
use crate::parser::ast::func_call2::FuncCall;
use crate::parser::ast::i64_lit::I64Lit;
use crate::parser::ast::index::Index;
use crate::parser::ast::lambda::LambdaDecl;
use crate::parser::ast::member::MemberAccess2;
use crate::parser::ast::op::Operator;
use crate::parser::ast::r#enum::EnumVariantInit;
use crate::parser::ast::r#struct::StructInit;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::sizeof::SizeOf;
use crate::parser::ast::str_lit::StrLit;
use crate::parser::ast::symbol::Symbol;
use crate::parser::ast::tuple::TupleInit;
use crate::parser::ast::u64_lit::U64Lit;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::source::Source;

/// Represents basic and composite expressions. For basic expressions, see `Expression::from_basic`,
/// and for composite expressions, see `Expression::from`.
#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub enum Expression {
    // Basic expressions.
    Symbol(Symbol), // TODO: Remove member access from this.
    BoolLiteral(BoolLit),
    I64Literal(I64Lit),
    U64Literal(U64Lit),
    StrLiteral(StrLit),
    FunctionCall(FunctionCall), // TODO: Remove.
    FunctionCall2(Box<FuncCall>),
    AnonFunction(Box<Function>),
    Lambda(Box<Function>),
    StructInit(StructInit),
    EnumInit(EnumVariantInit),
    TupleInit(TupleInit),
    ArrayInit(Box<ArrayInit>),
    SizeOf(SizeOf),
    Index(Box<Index>),
    MemberAccess(Box<MemberAccess2>),

    // Composite expressions.
    UnaryOperation(Operator, Box<Expression>),
    BinaryOperation(Box<Expression>, Operator, Box<Expression>),
    TypeCast(Box<Expression>, Type),
}

impl Display for Expression {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Expression::Symbol(s) => write!(f, "{}", s),
            Expression::BoolLiteral(b) => write!(f, "{}", b),
            Expression::I64Literal(i) => write!(f, "{}", i),
            Expression::U64Literal(i) => write!(f, "{}", i),
            Expression::StrLiteral(s) => write!(f, "{}", s),
            Expression::FunctionCall(chain) => write!(f, "{}", chain),
            Expression::FunctionCall2(call) => write!(f, "{}", call),
            Expression::AnonFunction(func) => write!(f, "{}", func),
            Expression::Lambda(func) => write!(f, "{}", func),
            Expression::UnaryOperation(op, expr) => write!(f, "{}{}", op, expr),
            Expression::BinaryOperation(left_expr, op, right_expr) => {
                write!(f, "{} {} {}", left_expr, op, right_expr)
            }
            Expression::StructInit(struct_init) => {
                write!(f, "struct initialization {}", struct_init)
            }
            Expression::EnumInit(enum_init) => write!(f, "enum initialization {}", enum_init),
            Expression::TupleInit(tuple_init) => write!(f, "tuple initialization {}", tuple_init),
            Expression::ArrayInit(array_init) => write!(f, "array initialization {}", array_init),
            Expression::SizeOf(so) => write!(f, "{}", so),
            Expression::Index(idx) => write!(f, "{}", idx),
            Expression::MemberAccess(m) => write!(f, "{}", m),
            Expression::TypeCast(expr, target_type) => {
                write!(f, "{} as {}", expr, target_type)
            }
        }
    }
}

impl Locatable for Expression {
    fn start_pos(&self) -> &Position {
        match self {
            Expression::Symbol(sym) => sym.start_pos(),
            Expression::BoolLiteral(bool_lit) => bool_lit.start_pos(),
            Expression::I64Literal(i64_lit) => i64_lit.start_pos(),
            Expression::U64Literal(u64_lit) => u64_lit.start_pos(),
            Expression::StrLiteral(string_lit) => string_lit.start_pos(),
            Expression::FunctionCall(fn_call) => fn_call.start_pos(),
            Expression::FunctionCall2(fn_call) => fn_call.start_pos(),
            Expression::AnonFunction(func) => func.start_pos(),
            Expression::Lambda(func) => func.start_pos(),
            Expression::UnaryOperation(_, expr) => expr.start_pos(),
            Expression::StructInit(struct_init) => struct_init.start_pos(),
            Expression::EnumInit(enum_init) => enum_init.start_pos(),
            Expression::TupleInit(tuple_init) => tuple_init.start_pos(),
            Expression::ArrayInit(array_init) => array_init.start_pos(),
            Expression::BinaryOperation(left, _, _) => left.start_pos(),
            Expression::SizeOf(so) => so.start_pos(),
            Expression::Index(idx) => idx.start_pos(),
            Expression::MemberAccess(m) => m.start_pos(),
            Expression::TypeCast(expr, _) => expr.start_pos(),
        }
    }

    fn end_pos(&self) -> &Position {
        match self {
            Expression::Symbol(sym) => sym.end_pos(),
            Expression::BoolLiteral(bool_lit) => bool_lit.end_pos(),
            Expression::I64Literal(i64_lit) => i64_lit.end_pos(),
            Expression::U64Literal(u64_lit) => u64_lit.end_pos(),
            Expression::StrLiteral(string_lit) => string_lit.end_pos(),
            Expression::FunctionCall(fn_call) => fn_call.end_pos(),
            Expression::FunctionCall2(fn_call) => fn_call.end_pos(),
            Expression::AnonFunction(func) => func.end_pos(),
            Expression::Lambda(func) => func.end_pos(),
            Expression::UnaryOperation(_, expr) => expr.end_pos(),
            Expression::StructInit(struct_init) => struct_init.end_pos(),
            Expression::EnumInit(enum_init) => enum_init.end_pos(),
            Expression::TupleInit(tuple_init) => tuple_init.end_pos(),
            Expression::ArrayInit(array_init) => array_init.end_pos(),
            Expression::BinaryOperation(left, _, _) => left.end_pos(),
            Expression::SizeOf(so) => so.end_pos(),
            Expression::Index(idx) => idx.end_pos(),
            Expression::MemberAccess(m) => m.end_pos(),
            Expression::TypeCast(_, target_type) => target_type.end_pos(),
        }
    }
}

impl Expression {
    /// Parses a basic or composite expression from the given tokens. A basic expression can be any
    /// of the following:
    ///  - a symbol (see `Symbol::from`)
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
    pub fn from(tokens: &mut Stream<Token>) -> ParseResult<Expression> {
        parse_expr(tokens)
    }
}

#[derive(Debug)]
enum OutNode {
    Expr(Expression),
    BinOp(Operator),
}

impl Display for OutNode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self {
            OutNode::Expr(e) => write!(f, "{}", e),
            OutNode::BinOp(o) => write!(f, "{}", o),
        }
    }
}

/// Parses expressions of the forms
///
///     <basic> [<binop> <comp>]*
///     <unop> <basic> [<binop> <comp>]*
///     sizeof type [<binop> <comp>]*
///     <basic> as <type> [<binop> <comp>]*
///
/// where
/// - `basic` is a basic expression (see `parse_basic`)
/// - `binop` is a binary operator
/// - `unop` is a unary operator
/// - `comp` is a composite expression (an expression containing binary operators)
/// - `type` is a type.
pub fn parse_expr(tokens: &mut Stream<Token>) -> ParseResult<Expression> {
    let mut op_stack: VecDeque<Token> = VecDeque::new();
    let mut out_q: VecDeque<OutNode> = VecDeque::new();

    // Collect nodes into the output queue in RPN order.
    while tokens.has_next() {
        // The expression must begin with either a basic expression (i.e. not a binary operator)
        // or a unary operator.
        let token = tokens.peek_next().unwrap();

        // Check if the expression is a unary operation, a `sizeof` (which is not considered
        // an operator because its operand is a type and not an expression), or just a basic
        // expression without operators.
        let expr = if let Some(op) = Operator::from(&token.kind) {
            // The operator should not be binary since it is at the beginning of the expression.
            if !op.is_unary() {
                return Err(ParseError::new_with_token(
                    ErrorKind::ExpectedBeginExpr,
                    format_code!(
                        "expected beginning of expression, but found binary operator {}",
                        op
                    )
                    .as_str(),
                    token.clone(),
                ));
            }

            // Parse all leading unary operators.
            let mut unary_ops = parse_unary_operators(tokens);

            // Form new expression from chained unary operators.
            let mut expr = parse_basic_expr(tokens)?;
            while let Some(op) = unary_ops.pop() {
                expr = Expression::UnaryOperation(op, Box::new(expr))
            }

            expr
        } else if token.kind == TokenKind::SizeOf {
            Expression::SizeOf(SizeOf::from(tokens)?)
        } else {
            parse_basic_expr(tokens)?
        };

        // Check if a type cast follows the expression.
        if let Some(Token {
            kind: TokenKind::As,
            ..
        }) = tokens.peek_next()
        {
            tokens.next();
            let typ = Type::from(tokens)?;
            out_q.push_back(OutNode::Expr(Expression::TypeCast(Box::new(expr), typ)));
        } else {
            out_q.push_back(OutNode::Expr(expr));
        }

        // Check if the expression is followed by a binary operator.
        match tokens.peek_next() {
            // There are more tokens in the sequence that might be part of this expression.
            // Check for optional binary operator or `as` type cast operator.
            Some(t) => match Operator::from(&t.kind) {
                Some(op) if op.is_binary() => {
                    let token = t.clone();
                    tokens.next();

                    // Do the part of the Shunting Yard algorithm where we push operations
                    // on the operator stack with lower precedence to the output queue.
                    while let Some(stack_op_token) = op_stack.back() {
                        let stack_op = Operator::from(&stack_op_token.kind).unwrap();
                        if stack_op.precedence() > op.precedence()
                            || (stack_op.precedence() == op.precedence()
                                && op.is_left_associative())
                        {
                            op_stack.pop_back();
                            out_q.push_back(OutNode::BinOp(stack_op));
                        } else {
                            break;
                        }
                    }

                    op_stack.push_back(token)
                }

                _ => break,
            },

            // There are no more tokens, so this must be the end of the expression.
            None => break,
        };
    }

    // Pop the remaining operators from the operator stack and onto the output queue.
    while let Some(token) = op_stack.pop_back() {
        out_q.push_back(OutNode::BinOp(Operator::from(&token.kind).unwrap()));
    }

    // Create expression tree from output queue in RPN order.
    Ok(parse_from_rpn(&mut out_q)?)
}

/// Parses and returns all sequential unary operators at the current position in the token stream.
fn parse_unary_operators(tokens: &mut Stream<Token>) -> Vec<Operator> {
    let mut unary_ops = vec![];
    while let Some(token) = tokens.peek_next() {
        match Operator::from(&token.kind) {
            Some(op) if op.is_unary() => {
                unary_ops.push(op);
                tokens.next();
            }
            _ => break,
        }
    }

    unary_ops
}

/// Returns an expression parsed from the vec of output notes in RPN form.
fn parse_from_rpn(rpn_queue: &mut VecDeque<OutNode>) -> ParseResult<Expression> {
    match rpn_queue.pop_back() {
        Some(OutNode::Expr(expr)) => Ok(expr),

        Some(OutNode::BinOp(op)) => {
            let right = parse_from_rpn(rpn_queue)?;
            let left = parse_from_rpn(rpn_queue)?;
            Ok(Expression::BinaryOperation(
                Box::new(left),
                op,
                Box::new(right),
            ))
        }

        None => {
            return Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "unexpected end of expression",
                None,
                Position::default(),
                Position::default(),
            ))
        }
    }
}

/// Parses a basic expression. Expects token sequences of the following forms
///
///     <unit>
///     <unit>\[comp\]*
///     <unit>(comp,*)
///     <unit>.*
///
/// where
/// - `unit` is a unitary expression (see `parse_unit`)
/// - `comp` is a composite expression (see `parse_expr`).
fn parse_basic_expr(tokens: &mut Stream<Token>) -> ParseResult<Expression> {
    let mut expr = parse_unit_expr(tokens)?;

    loop {
        let token = match tokens.peek_next() {
            Some(t) => t,
            None => {
                return Ok(expr);
            }
        };

        match &token.kind {
            // TODO: move call parsing into its own fn
            TokenKind::LeftParen => {
                tokens.next();

                // Collect call arguments.
                let mut args = vec![];
                loop {
                    if let Some(Token { end, .. }) =
                        Source::parse_optional(tokens, TokenKind::RightParen)
                    {
                        expr = Expression::FunctionCall2(Box::new(FuncCall::new(
                            expr,
                            args,
                            end.clone(),
                        )));
                        break;
                    }

                    let arg = parse_expr(tokens)?;
                    args.push(arg);

                    if let Token {
                        kind: TokenKind::RightParen,
                        end,
                        ..
                    } = Source::parse_expecting_any(
                        tokens,
                        HashSet::from([TokenKind::Comma, TokenKind::RightParen]),
                    )? {
                        expr = Expression::FunctionCall2(Box::new(FuncCall::new(
                            expr,
                            args,
                            end.clone(),
                        )));
                        break;
                    };
                }
            }

            // TODO: move index parsing into its own fn
            TokenKind::LeftBracket => {
                tokens.next();

                expr = Expression::Index(Box::new(Index::new(expr, parse_expr(tokens)?)));
                Source::parse_expecting(tokens, TokenKind::RightBracket)?;
            }

            TokenKind::Dot => {
                tokens.next();

                let (member_name, start_pos, end_pos) = match tokens.next() {
                    Some(Token {
                        kind: TokenKind::Identifier(name),
                        start,
                        end,
                    }) => (name.clone(), start.clone(), end.clone()),

                    Some(Token {
                        kind: TokenKind::I64Literal(index, false),
                        start,
                        end,
                    }) => (index.to_string(), start.clone(), end.clone()),

                    Some(other) => {
                        return Err(ParseError::new_with_token(
                            ErrorKind::ExpectedIdent,
                            format_code!("expected identifier, but found {}", other).as_str(),
                            other.clone(),
                        ))
                    }

                    None => {
                        return Err(ParseError::new(
                            ErrorKind::UnexpectedEOF,
                            "expected identifier, but found EOF",
                            None,
                            Position::default(),
                            Position::default(),
                        ))
                    }
                };

                expr = Expression::MemberAccess(Box::new(MemberAccess2::new(
                    expr,
                    member_name,
                    start_pos,
                    end_pos,
                )));
            }

            _ => return Ok(expr),
        }
    }
}

/// Parses a unitary expression. Expects token sequences of the forms
///
///     (<comp>)
///     <array_init>
///     <tuple_init>
///     <struct_init>
///     <enum_init>
///     <literal>
///     <symbol>
///
/// where
/// `comp` is a composite expression (see `parse_expr`).
fn parse_unit_expr(tokens: &mut Stream<Token>) -> ParseResult<Expression> {
    let token = match tokens.peek_next() {
        Some(t) => t,
        None => {
            return Err(ParseError::new(
                ErrorKind::UnexpectedEOF,
                "expected expression, but found EOF",
                None,
                Position::default(),
                Position::default(),
            ))
        }
    };

    let expr = match &token.kind {
        // Basic literals.
        TokenKind::BoolLiteral(_) => Expression::BoolLiteral(BoolLit::from(tokens)?),
        TokenKind::I64Literal(_, _) => Expression::I64Literal(I64Lit::from(tokens)?),
        TokenKind::U64Literal(_, _) => Expression::U64Literal(U64Lit::from(tokens)?),
        TokenKind::StrLiteral(_) => Expression::StrLiteral(StrLit::from(tokens)?),

        // Composite value initialization.
        TokenKind::LeftBracket => Expression::ArrayInit(Box::new(ArrayInit::from(tokens)?)),
        TokenKind::LeftBrace => Expression::TupleInit(TupleInit::from(tokens)?),
        TokenKind::Struct => Expression::StructInit(StructInit::from(tokens)?),

        // Inline function declarations.
        TokenKind::Fn => Expression::AnonFunction(Box::new(Function::from_anon(tokens)?)),
        TokenKind::DollarSign => {
            Expression::Lambda(Box::new(Function::from_lambda(LambdaDecl::from(tokens)?)))
        }

        // Parenthesized expressions.
        TokenKind::LeftParen => {
            tokens.next();
            let expr = parse_expr(tokens)?;
            Source::parse_expecting(tokens, TokenKind::RightParen)?;
            expr
        }

        // Any expression that begins with an identifier.
        TokenKind::Identifier(_) => match tokens.peek_ahead(1) {
            Some(Token {
                kind: TokenKind::DoubleColon,
                ..
            }) => Expression::EnumInit(EnumVariantInit::from(tokens)?),

            Some(Token {
                kind: TokenKind::LeftBrace,
                ..
            }) => {
                // This might be struct initialization, or just part of a conditional that is
                // followed by the conditional closure.
                let cursor = tokens.cursor();
                if let Ok(struct_init) = StructInit::from(tokens) {
                    return Ok(Expression::StructInit(struct_init));
                }

                tokens.set_cursor(cursor);
                Expression::Symbol(Symbol::from_identifier(tokens)?)
            }

            _ => Expression::Symbol(Symbol::from_identifier(tokens)?),
        },

        other => {
            return Err(ParseError::new_with_token(
                ErrorKind::ExpectedExpr,
                format_code!("expected expression, but found {}", other).as_str(),
                token.clone(),
            ))
        }
    };

    Ok(expr)
}

#[cfg(test)]
mod tests {
    use crate::lexer::lex::lex;
    use crate::lexer::pos::Position;
    use crate::lexer::stream::Stream;
    use crate::lexer::token::Token;
    use crate::lexer::token_kind::TokenKind;
    use crate::parser::ast::bool_lit::BoolLit;
    use crate::parser::ast::expr::Expression;
    use crate::parser::ast::func_call2::FuncCall;
    use crate::parser::ast::i64_lit::I64Lit;
    use crate::parser::ast::op::Operator;
    use crate::parser::ast::str_lit::StrLit;
    use crate::parser::ast::symbol::Symbol;
    use crate::parser::error::{ErrorKind, ParseError, ParseResult};

    fn parse(raw: &str) -> ParseResult<Expression> {
        let tokens = lex(&mut Stream::from(raw.chars().collect())).expect("should succeed");
        Expression::from(&mut Stream::from(tokens))
    }

    #[test]
    fn parse_basic_var_value() {
        assert_eq!(
            parse(r#"my_var"#).unwrap(),
            Expression::Symbol(Symbol {
                name: "my_var".to_string(),
                member_access: None,
                start_pos: Position::new(1, 1),
                end_pos: Position::new(1, 7),
            })
        );
    }

    #[test]
    fn parse_basic_bool_literal() {
        assert_eq!(
            parse("true").unwrap(),
            Expression::BoolLiteral(BoolLit::new(true, Position::new(1, 1), Position::new(1, 5)))
        );
        assert_eq!(
            parse("false").unwrap(),
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
            parse("123").unwrap(),
            Expression::I64Literal(I64Lit {
                value: 123,
                has_type_suffix: false,
                start_pos: Position::new(1, 1),
                end_pos: Position::new(1, 4),
            })
        );
    }

    #[test]
    fn parse_basic_string_literal() {
        assert_eq!(
            parse(r#""this is my \"String\"""#).unwrap(),
            Expression::StrLiteral(StrLit {
                value: r#"this is my "String""#.to_string(),
                start_pos: Position::new(1, 1),
                end_pos: Position::new(1, 24),
            })
        );
    }

    #[test]
    fn parse_function_call() {
        assert_eq!(
            parse("call(3 * 2 - 2, other(!thing, 1 > var % 2))").unwrap(),
            Expression::FunctionCall2(Box::new(FuncCall::new(
                Expression::Symbol(Symbol::new(
                    "call",
                    Position::new(1, 1),
                    Position::new(1, 5)
                )),
                vec![
                    Expression::BinaryOperation(
                        Box::new(Expression::BinaryOperation(
                            Box::new(Expression::I64Literal(I64Lit {
                                value: 3,
                                has_type_suffix: false,
                                start_pos: Position::new(1, 6),
                                end_pos: Position::new(1, 7),
                            })),
                            Operator::Multiply,
                            Box::new(Expression::I64Literal(I64Lit {
                                value: 2,
                                has_type_suffix: false,
                                start_pos: Position::new(1, 10),
                                end_pos: Position::new(1, 11),
                            }))
                        )),
                        Operator::Subtract,
                        Box::new(Expression::I64Literal(I64Lit {
                            value: 2,
                            has_type_suffix: false,
                            start_pos: Position::new(1, 14),
                            end_pos: Position::new(1, 15),
                        }))
                    ),
                    Expression::FunctionCall2(Box::new(FuncCall::new(
                        Expression::Symbol(Symbol::new(
                            "other",
                            Position::new(1, 17),
                            Position::new(1, 22)
                        )),
                        vec![
                            Expression::UnaryOperation(
                                Operator::LogicalNot,
                                Box::new(Expression::Symbol(Symbol {
                                    name: "thing".to_string(),
                                    member_access: None,
                                    start_pos: Position::new(1, 24),
                                    end_pos: Position::new(1, 29),
                                }))
                            ),
                            Expression::BinaryOperation(
                                Box::new(Expression::I64Literal(I64Lit {
                                    value: 1,
                                    has_type_suffix: false,
                                    start_pos: Position::new(1, 31),
                                    end_pos: Position::new(1, 32),
                                })),
                                Operator::GreaterThan,
                                Box::new(Expression::BinaryOperation(
                                    Box::new(Expression::Symbol(Symbol {
                                        name: "var".to_string(),
                                        member_access: None,
                                        start_pos: Position::new(1, 35),
                                        end_pos: Position::new(1, 38),
                                    })),
                                    Operator::Modulo,
                                    Box::new(Expression::I64Literal(I64Lit {
                                        value: 2,
                                        has_type_suffix: false,
                                        start_pos: Position::new(1, 41),
                                        end_pos: Position::new(1, 42),
                                    }))
                                ))
                            )
                        ],
                        Position::new(1, 43)
                    )))
                ],
                Position::new(1, 44)
            )))
        );
    }

    #[test]
    fn parse_i64_arithmetic() {
        assert_eq!(
            parse("(3 + 6) / 3 - 5 + 298 * 3").unwrap(),
            Expression::BinaryOperation(
                Box::new(Expression::BinaryOperation(
                    Box::new(Expression::BinaryOperation(
                        Box::new(Expression::BinaryOperation(
                            Box::new(Expression::I64Literal(I64Lit {
                                value: 3,
                                has_type_suffix: false,
                                start_pos: Position::new(1, 2),
                                end_pos: Position::new(1, 3),
                            })),
                            Operator::Add,
                            Box::new(Expression::I64Literal(I64Lit {
                                value: 6,
                                has_type_suffix: false,
                                start_pos: Position::new(1, 6),
                                end_pos: Position::new(1, 7),
                            }))
                        )),
                        Operator::Divide,
                        Box::new(Expression::I64Literal(I64Lit {
                            value: 3,
                            has_type_suffix: false,
                            start_pos: Position::new(1, 11),
                            end_pos: Position::new(1, 12),
                        }))
                    )),
                    Operator::Subtract,
                    Box::new(Expression::I64Literal(I64Lit {
                        value: 5,
                        has_type_suffix: false,
                        start_pos: Position::new(1, 15),
                        end_pos: Position::new(1, 16),
                    }))
                )),
                Operator::Add,
                Box::new(Expression::BinaryOperation(
                    Box::new(Expression::I64Literal(I64Lit {
                        value: 298,
                        has_type_suffix: false,
                        start_pos: Position::new(1, 19),
                        end_pos: Position::new(1, 22),
                    })),
                    Operator::Multiply,
                    Box::new(Expression::I64Literal(I64Lit {
                        value: 3,
                        has_type_suffix: false,
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
            parse(raw).unwrap(),
            Expression::BinaryOperation(
                Box::new(Expression::BinaryOperation(
                    Box::new(Expression::BinaryOperation(
                        Box::new(Expression::BinaryOperation(
                            Box::new(Expression::Symbol(Symbol {
                                name: "var".to_string(),
                                member_access: None,
                                start_pos: Position::new(1, 2),
                                end_pos: Position::new(1, 5),
                            })),
                            Operator::Subtract,
                            Box::new(Expression::I64Literal(I64Lit {
                                value: 3,
                                has_type_suffix: false,
                                start_pos: Position::new(1, 8),
                                end_pos: Position::new(1, 9)
                            })),
                        )),
                        Operator::Divide,
                        Box::new(Expression::I64Literal(I64Lit {
                            value: 4,
                            has_type_suffix: false,
                            start_pos: Position::new(1, 13),
                            end_pos: Position::new(1, 14)
                        })),
                    )),
                    Operator::Multiply,
                    Box::new(Expression::BinaryOperation(
                        Box::new(Expression::FunctionCall2(Box::new(FuncCall::new(
                            Expression::Symbol(Symbol::new(
                                "call",
                                Position::new(2, 2),
                                Position::new(2, 6)
                            )),
                            vec![Expression::BoolLiteral(BoolLit {
                                value: true,
                                start_pos: Position::new(2, 7),
                                end_pos: Position::new(2, 11)
                            })],
                            Position::new(2, 12)
                        )))),
                        Operator::Modulo,
                        Box::new(Expression::I64Literal(I64Lit {
                            value: 2,
                            has_type_suffix: false,
                            start_pos: Position::new(2, 15),
                            end_pos: Position::new(2, 16)
                        })),
                    )),
                )),
                Operator::Add,
                Box::new(Expression::I64Literal(I64Lit {
                    value: 5,
                    has_type_suffix: false,
                    start_pos: Position::new(3, 1),
                    end_pos: Position::new(3, 2)
                })),
            )
        );
    }

    #[test]
    fn parse_unmatched_open_paren() {
        let result = parse("3 - 4 / (2 * 3:");
        assert!(matches!(
            result,
            Err(ParseError {
                kind: ErrorKind::UnexpectedToken,
                message: _,
                token: Some(Token {
                    kind: TokenKind::Colon,
                    start: Position { line: 1, col: 15 },
                    end: Position { line: 1, col: 16 },
                }),
                start_pos: Position { line: 1, col: 15 },
                end_pos: Position { line: 1, col: 16 },
            })
        ));
    }

    #[test]
    fn parse_composite_negative_values() {
        let result = parse("-8 - (-100 + 2) * 4 / 2 + 8").unwrap();
        assert_eq!(
            result,
            Expression::BinaryOperation(
                Box::new(Expression::BinaryOperation(
                    Box::new(Expression::UnaryOperation(
                        Operator::Subtract,
                        Box::new(Expression::I64Literal(I64Lit {
                            value: 8,
                            has_type_suffix: false,
                            start_pos: Position::new(1, 2),
                            end_pos: Position::new(1, 3),
                        })),
                    )),
                    Operator::Subtract,
                    Box::new(Expression::BinaryOperation(
                        Box::new(Expression::BinaryOperation(
                            Box::new(Expression::BinaryOperation(
                                Box::new(Expression::UnaryOperation(
                                    Operator::Subtract,
                                    Box::new(Expression::I64Literal(I64Lit {
                                        value: 100,
                                        has_type_suffix: false,
                                        start_pos: Position::new(1, 8),
                                        end_pos: Position::new(1, 11),
                                    }))
                                )),
                                Operator::Add,
                                Box::new(Expression::I64Literal(I64Lit {
                                    value: 2,
                                    has_type_suffix: false,
                                    start_pos: Position::new(1, 14),
                                    end_pos: Position::new(1, 15)
                                })),
                            )),
                            Operator::Multiply,
                            Box::new(Expression::I64Literal(I64Lit {
                                value: 4,
                                has_type_suffix: false,
                                start_pos: Position::new(1, 19),
                                end_pos: Position::new(1, 20)
                            })),
                        )),
                        Operator::Divide,
                        Box::new(Expression::I64Literal(I64Lit {
                            value: 2,
                            has_type_suffix: false,
                            start_pos: Position::new(1, 23),
                            end_pos: Position::new(1, 24)
                        })),
                    )),
                )),
                Operator::Add,
                Box::new(Expression::I64Literal(I64Lit {
                    value: 8,
                    has_type_suffix: false,
                    start_pos: Position::new(1, 27),
                    end_pos: Position::new(1, 28)
                })),
            )
        );
    }

    #[test]
    fn parse_basic_negative_values() {
        let result = parse("-8").unwrap();
        assert_eq!(
            result,
            Expression::UnaryOperation(
                Operator::Subtract,
                Box::new(Expression::I64Literal(I64Lit {
                    value: 8,
                    has_type_suffix: false,
                    start_pos: Position::new(1, 2),
                    end_pos: Position::new(1, 3),
                })),
            )
        );

        let result = parse("-x").unwrap();
        assert_eq!(
            result,
            Expression::UnaryOperation(
                Operator::Subtract,
                Box::new(Expression::Symbol(Symbol {
                    name: "x".to_string(),
                    member_access: None,
                    start_pos: Position::new(1, 2),
                    end_pos: Position::new(1, 3),
                })),
            )
        );

        let result = parse("-f()").unwrap();
        assert_eq!(
            result,
            Expression::UnaryOperation(
                Operator::Subtract,
                Box::new(Expression::FunctionCall2(Box::new(FuncCall::new(
                    Expression::Symbol(Symbol::new("f", Position::new(1, 2), Position::new(1, 3))),
                    vec![],
                    Position::new(1, 5),
                ))))
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
            let result = parse(input);
            assert!(matches!(
                result,
                Err(ParseError {
                    kind: ErrorKind::ExpectedBeginExpr,
                    ..
                })
            ))
        }
    }

    #[test]
    fn parse_redundant_parens() {
        let result = parse("(((1>0)+1))").unwrap();
        assert_eq!(
            result,
            Expression::BinaryOperation(
                Box::new(Expression::BinaryOperation(
                    Box::new(Expression::I64Literal(I64Lit {
                        value: 1,
                        has_type_suffix: false,
                        start_pos: Position::new(1, 4),
                        end_pos: Position::new(1, 5)
                    })),
                    Operator::GreaterThan,
                    Box::new(Expression::I64Literal(I64Lit {
                        value: 0,
                        has_type_suffix: false,
                        start_pos: Position::new(1, 6),
                        end_pos: Position::new(1, 7)
                    })),
                )),
                Operator::Add,
                Box::new(Expression::I64Literal(I64Lit {
                    value: 1,
                    has_type_suffix: false,
                    start_pos: Position::new(1, 9),
                    end_pos: Position::new(1, 10)
                })),
            )
        )
    }

    #[test]
    fn parse_unexpected_end_of_expr() {
        for input in ["2 -", "ok *", "5/", "v -3 + -", "(3 % 3) +"] {
            let result = parse(input);
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
        let result = parse("--(-v--a)-2--(-100 -- call(1))").expect("should succeed");
        assert_eq!(
            result,
            Expression::BinaryOperation(
                Box::new(Expression::BinaryOperation(
                    Box::new(Expression::UnaryOperation(
                        Operator::Subtract,
                        Box::new(Expression::UnaryOperation(
                            Operator::Subtract,
                            Box::new(Expression::BinaryOperation(
                                Box::new(Expression::UnaryOperation(
                                    Operator::Subtract,
                                    Box::new(Expression::Symbol(Symbol {
                                        name: "v".to_string(),
                                        member_access: None,
                                        start_pos: Position { line: 1, col: 5 },
                                        end_pos: Position { line: 1, col: 6 },
                                    }))
                                )),
                                Operator::Subtract,
                                Box::new(Expression::UnaryOperation(
                                    Operator::Subtract,
                                    Box::new(Expression::Symbol(Symbol {
                                        name: "a".to_string(),
                                        member_access: None,
                                        start_pos: Position { line: 1, col: 8 },
                                        end_pos: Position { line: 1, col: 9 },
                                    }))
                                )),
                            )),
                        )),
                    )),
                    Operator::Subtract,
                    Box::new(Expression::I64Literal(I64Lit {
                        value: 2,
                        has_type_suffix: false,
                        start_pos: Position { line: 1, col: 11 },
                        end_pos: Position { line: 1, col: 12 },
                    })),
                )),
                Operator::Subtract,
                Box::new(Expression::UnaryOperation(
                    Operator::Subtract,
                    Box::new(Expression::BinaryOperation(
                        Box::new(Expression::UnaryOperation(
                            Operator::Subtract,
                            Box::new(Expression::I64Literal(I64Lit {
                                value: 100,
                                has_type_suffix: false,
                                start_pos: Position { line: 1, col: 16 },
                                end_pos: Position { line: 1, col: 19 },
                            })),
                        )),
                        Operator::Subtract,
                        Box::new(Expression::UnaryOperation(
                            Operator::Subtract,
                            Box::new(Expression::FunctionCall2(Box::new(FuncCall {
                                fn_expr: Expression::Symbol(Symbol {
                                    name: "call".to_string(),
                                    member_access: None,
                                    start_pos: Position { line: 1, col: 23 },
                                    end_pos: Position { line: 1, col: 27 },
                                },),
                                args: vec![Expression::I64Literal(I64Lit {
                                    value: 1,
                                    has_type_suffix: false,
                                    start_pos: Position { line: 1, col: 28 },
                                    end_pos: Position { line: 1, col: 29 },
                                })],
                                start_pos: Position { line: 1, col: 23 },
                                end_pos: Position { line: 1, col: 30 },
                            }))),
                        )),
                    ))
                ))
            )
        );
    }

    #[test]
    fn redundant_parenthesized_negatives() {
        let result = parse("-(-b-(-100))").unwrap();
        assert_eq!(
            result,
            Expression::UnaryOperation(
                Operator::Subtract,
                Box::new(Expression::BinaryOperation(
                    Box::new(Expression::UnaryOperation(
                        Operator::Subtract,
                        Box::new(Expression::Symbol(Symbol {
                            name: "b".to_string(),
                            member_access: None,
                            start_pos: Position::new(1, 4),
                            end_pos: Position::new(1, 5),
                        })),
                    )),
                    Operator::Subtract,
                    Box::new(Expression::UnaryOperation(
                        Operator::Subtract,
                        Box::new(Expression::I64Literal(I64Lit {
                            value: 100,
                            has_type_suffix: false,
                            start_pos: Position::new(1, 8),
                            end_pos: Position::new(1, 11),
                        })),
                    )),
                )),
            )
        )
    }
}
