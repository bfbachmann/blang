use std::collections::VecDeque;
use std::fmt;
use std::fmt::{Display, Formatter};

use crate::lexer::pos::{Locatable, Position, Span};
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::array::ArrayInit;
use crate::parser::ast::bool_lit::BoolLit;
use crate::parser::ast::char_lit::CharLit;
use crate::parser::ast::f32_lit::F32Lit;
use crate::parser::ast::f64_lit::F64Lit;
use crate::parser::ast::from::From;
use crate::parser::ast::func::Function;
use crate::parser::ast::func_call::FuncCall;
use crate::parser::ast::i16_lit::I16Lit;
use crate::parser::ast::i32_lit::I32Lit;
use crate::parser::ast::i64_lit::I64Lit;
use crate::parser::ast::i8_lit::I8Lit;
use crate::parser::ast::index::Index;
use crate::parser::ast::int_lit::IntLit;
use crate::parser::ast::lambda::LambdaDecl;
use crate::parser::ast::member::MemberAccess;
use crate::parser::ast::op::Operator;
use crate::parser::ast::r#enum::EnumVariantInit;
use crate::parser::ast::r#struct::StructInit;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::sizeof::SizeOf;
use crate::parser::ast::str_lit::StrLit;
use crate::parser::ast::symbol::Symbol;
use crate::parser::ast::tuple::TupleInit;
use crate::parser::ast::u16_lit::U16Lit;
use crate::parser::ast::u32_lit::U32Lit;
use crate::parser::ast::u64_lit::U64Lit;
use crate::parser::ast::u8_lit::U8Lit;
use crate::parser::ast::uint_lit::UintLit;
use crate::parser::error::ParseResult;
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::module::Module;

/// Represents basic and composite expressions. For basic expressions, see `Expression::from_basic`,
/// and for composite expressions, see `Expression::from`.
#[derive(Debug, PartialEq, Clone, Eq, Hash)]
pub enum Expression {
    // Basic expressions.
    Symbol(Symbol),
    BoolLiteral(BoolLit),
    I8Literal(I8Lit),
    U8Literal(U8Lit),
    I16Literal(I16Lit),
    U16Literal(U16Lit),
    I32Literal(I32Lit),
    U32Literal(U32Lit),
    F32Literal(F32Lit),
    I64Literal(I64Lit),
    U64Literal(U64Lit),
    F64Literal(F64Lit),
    IntLiteral(IntLit),
    UintLiteral(UintLit),
    StrLiteral(StrLit),
    CharLiteral(CharLit),
    FunctionCall(Box<FuncCall>),
    AnonFunction(Box<Function>),
    Lambda(Box<Function>),
    StructInit(StructInit),
    EnumInit(EnumVariantInit),
    TupleInit(TupleInit),
    ArrayInit(Box<ArrayInit>),
    SizeOf(SizeOf),
    Index(Box<Index>),
    MemberAccess(Box<MemberAccess>),

    // Composite expressions.
    UnaryOperation(Operator, Box<Expression>),
    BinaryOperation(Box<Expression>, Operator, Box<Expression>),
    TypeCast(Box<Expression>, Type),

    // Statements as expressions.
    From(From),
}

impl Display for Expression {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Expression::Symbol(s) => write!(f, "{}", s),
            Expression::BoolLiteral(b) => write!(f, "{}", b),
            Expression::I8Literal(i) => write!(f, "{}", i),
            Expression::U8Literal(i) => write!(f, "{}", i),
            Expression::I16Literal(i) => write!(f, "{}", i),
            Expression::U16Literal(i) => write!(f, "{}", i),
            Expression::I32Literal(i) => write!(f, "{}", i),
            Expression::U32Literal(i) => write!(f, "{}", i),
            Expression::F32Literal(i) => write!(f, "{}", i),
            Expression::I64Literal(i) => write!(f, "{}", i),
            Expression::U64Literal(i) => write!(f, "{}", i),
            Expression::F64Literal(i) => write!(f, "{}", i),
            Expression::IntLiteral(i) => write!(f, "{}", i),
            Expression::UintLiteral(i) => write!(f, "{}", i),
            Expression::StrLiteral(s) => write!(f, "{}", s),
            Expression::CharLiteral(c) => write!(f, "{}", c),
            Expression::FunctionCall(call) => write!(f, "{}", call),
            Expression::AnonFunction(func) => write!(f, "{}", func),
            Expression::Lambda(func) => write!(f, "{}", func),
            Expression::UnaryOperation(op, expr) => match op {
                Operator::Defererence => write!(f, "{}{}", expr, op),
                Operator::MutReference => write!(f, "{} {}", op, expr),
                _ => write!(f, "{}{}", op, expr),
            },
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
            Expression::From(from) => {
                write!(f, "from {}", from.statement)
            }
        }
    }
}

impl Locatable for Expression {
    fn start_pos(&self) -> &Position {
        match self {
            Expression::Symbol(sym) => sym.start_pos(),
            Expression::BoolLiteral(bool_lit) => bool_lit.start_pos(),
            Expression::I8Literal(i) => i.start_pos(),
            Expression::U8Literal(i) => i.start_pos(),
            Expression::I16Literal(i) => i.start_pos(),
            Expression::U16Literal(i) => i.start_pos(),
            Expression::I32Literal(i) => i.start_pos(),
            Expression::U32Literal(i) => i.start_pos(),
            Expression::F32Literal(i) => i.start_pos(),
            Expression::I64Literal(i) => i.start_pos(),
            Expression::U64Literal(i) => i.start_pos(),
            Expression::F64Literal(i) => i.start_pos(),
            Expression::IntLiteral(i) => i.start_pos(),
            Expression::UintLiteral(i) => i.start_pos(),
            Expression::StrLiteral(string_lit) => string_lit.start_pos(),
            Expression::CharLiteral(char_lit) => char_lit.start_pos(),
            Expression::FunctionCall(fn_call) => fn_call.start_pos(),
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
            Expression::From(from) => from.start_pos(),
        }
    }

    fn end_pos(&self) -> &Position {
        match self {
            Expression::Symbol(sym) => sym.end_pos(),
            Expression::BoolLiteral(bool_lit) => bool_lit.end_pos(),
            Expression::I8Literal(i) => i.end_pos(),
            Expression::U8Literal(i) => i.end_pos(),
            Expression::I16Literal(i) => i.end_pos(),
            Expression::U16Literal(i) => i.end_pos(),
            Expression::I32Literal(i) => i.end_pos(),
            Expression::U32Literal(i) => i.end_pos(),
            Expression::F32Literal(i) => i.end_pos(),
            Expression::I64Literal(i) => i.end_pos(),
            Expression::U64Literal(i) => i.end_pos(),
            Expression::F64Literal(i) => i.end_pos(),
            Expression::IntLiteral(i) => i.end_pos(),
            Expression::UintLiteral(i) => i.end_pos(),
            Expression::StrLiteral(string_lit) => string_lit.end_pos(),
            Expression::CharLiteral(char_lit) => char_lit.end_pos(),
            Expression::FunctionCall(fn_call) => fn_call.end_pos(),
            Expression::AnonFunction(func) => func.end_pos(),
            Expression::Lambda(func) => func.end_pos(),
            Expression::UnaryOperation(_, expr) => expr.end_pos(),
            Expression::StructInit(struct_init) => struct_init.end_pos(),
            Expression::EnumInit(enum_init) => enum_init.end_pos(),
            Expression::TupleInit(tuple_init) => tuple_init.end_pos(),
            Expression::ArrayInit(array_init) => array_init.end_pos(),
            Expression::BinaryOperation(_, _, right) => right.end_pos(),
            Expression::SizeOf(so) => so.end_pos(),
            Expression::Index(idx) => idx.end_pos(),
            Expression::MemberAccess(m) => m.end_pos(),
            Expression::TypeCast(_, target_type) => target_type.end_pos(),
            Expression::From(from) => from.end_pos(),
        }
    }

    fn span(&self) -> &Span {
        match self {
            Expression::Symbol(sym) => sym.span(),
            Expression::BoolLiteral(bool_lit) => bool_lit.span(),
            Expression::I8Literal(i) => i.span(),
            Expression::U8Literal(i) => i.span(),
            Expression::I16Literal(i) => i.span(),
            Expression::U16Literal(i) => i.span(),
            Expression::I32Literal(i) => i.span(),
            Expression::U32Literal(i) => i.span(),
            Expression::F32Literal(i) => i.span(),
            Expression::I64Literal(i) => i.span(),
            Expression::U64Literal(i) => i.span(),
            Expression::F64Literal(i) => i.span(),
            Expression::IntLiteral(i) => i.span(),
            Expression::UintLiteral(i) => i.span(),
            Expression::StrLiteral(string_lit) => string_lit.span(),
            Expression::CharLiteral(char_lit) => char_lit.span(),
            Expression::FunctionCall(fn_call) => fn_call.span(),
            Expression::AnonFunction(func) => func.span(),
            Expression::Lambda(func) => func.span(),
            Expression::UnaryOperation(_, expr) => expr.span(),
            Expression::StructInit(struct_init) => struct_init.span(),
            Expression::EnumInit(enum_init) => enum_init.span(),
            Expression::TupleInit(tuple_init) => tuple_init.span(),
            Expression::ArrayInit(array_init) => array_init.span(),
            Expression::BinaryOperation(_, _, right) => right.span(),
            Expression::SizeOf(so) => so.span(),
            Expression::Index(idx) => idx.span(),
            Expression::MemberAccess(m) => m.span(),
            Expression::TypeCast(_, target_type) => target_type.span(),
            Expression::From(from) => from.span(),
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
            // Make sure the operator is unary and is not a deref (because derefs are suffix
            // operators).
            Some(op) if op.is_unary() && op != Operator::Defererence => {
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
                Default::default(),
            ))
        }
    }
}

/// Parses a basic expression. Expects token sequences of the following forms
///
///     <unit>
///     <unit>.(comp)
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
            // The `(` token will only be considered part of this expression if
            // it is on the same line as the end of the expression. In other words,
            // if the `(` is on a new line, it won't be considered part of this
            // expression. This solves the problem of finding the end of an
            // expression when the is followed by a statement that starts with
            // `(` like
            //
            //      let mut a = my_variable
            //      (a) = 10
            //
            TokenKind::LeftParen if token.span.start_pos.line == expr.end_pos().line => {
                tokens.next();

                // Collect call arguments.
                let mut args = vec![];
                loop {
                    if let Some(Token { span, .. }) =
                        Module::parse_optional(tokens, TokenKind::RightParen)
                    {
                        expr = Expression::FunctionCall(Box::new(FuncCall::new(
                            expr,
                            args,
                            span.end_pos,
                        )));
                        break;
                    }

                    let arg = parse_expr(tokens)?;
                    args.push(arg);

                    if let Token {
                        kind: TokenKind::RightParen,
                        span,
                        ..
                    } = Module::parse_expecting_any(
                        tokens,
                        vec![TokenKind::Comma, TokenKind::RightParen],
                    )? {
                        expr = Expression::FunctionCall(Box::new(FuncCall::new(
                            expr,
                            args,
                            span.end_pos,
                        )));
                        break;
                    };
                }
            }

            TokenKind::BeginIndex => {
                tokens.next();

                expr = Expression::Index(Box::new(Index::new(expr, parse_expr(tokens)?)));
                Module::parse_expecting(tokens, TokenKind::RightParen)?;
            }

            TokenKind::Dot => {
                tokens.next();

                let member_symbol = Symbol::from(tokens)?;
                let start_pos = expr.start_pos().clone();
                let end_pos = member_symbol.end_pos().clone();

                expr = Expression::MemberAccess(Box::new(MemberAccess {
                    base_expr: expr,
                    member_symbol,
                    span: Span { start_pos, end_pos },
                }));
            }

            TokenKind::Deref => {
                tokens.next();
                expr = Expression::UnaryOperation(Operator::Defererence, Box::new(expr));
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
///     <pattern>
///     <literal>
///     <symbol>
///     <from>
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
                Default::default(),
            ))
        }
    };

    let expr = match &token.kind {
        // Basic literals.
        TokenKind::BoolLiteral(_) => Expression::BoolLiteral(BoolLit::from(tokens)?),
        TokenKind::I8Literal(_) => Expression::I8Literal(I8Lit::from(tokens)?),
        TokenKind::U8Literal(_) => Expression::U8Literal(U8Lit::from(tokens)?),
        TokenKind::I16Literal(_) => Expression::I16Literal(I16Lit::from(tokens)?),
        TokenKind::U16Literal(_) => Expression::U16Literal(U16Lit::from(tokens)?),
        TokenKind::I32Literal(_) => Expression::I32Literal(I32Lit::from(tokens)?),
        TokenKind::U32Literal(_) => Expression::U32Literal(U32Lit::from(tokens)?),
        TokenKind::F32Literal(_) => Expression::F32Literal(F32Lit::from(tokens)?),
        TokenKind::I64Literal(_) => Expression::I64Literal(I64Lit::from(tokens)?),
        TokenKind::U64Literal(_) => Expression::U64Literal(U64Lit::from(tokens)?),
        TokenKind::F64Literal(_) => Expression::F64Literal(F64Lit::from(tokens)?),
        TokenKind::IntLiteral(_) => Expression::IntLiteral(IntLit::from(tokens)?),
        TokenKind::UintLiteral(_) => Expression::UintLiteral(UintLit::from(tokens)?),
        TokenKind::StrLiteral(_) => Expression::StrLiteral(StrLit::from(tokens)?),
        TokenKind::CharLiteral(_) => Expression::CharLiteral(CharLit::from(tokens)?),

        // Composite value initialization.
        TokenKind::LeftBracket => Expression::ArrayInit(Box::new(ArrayInit::from(tokens)?)),
        TokenKind::LeftBrace => Expression::TupleInit(TupleInit::from(tokens)?),

        // Inline function declarations.
        TokenKind::Fn => Expression::AnonFunction(Box::new(Function::from_anon(tokens)?)),
        TokenKind::DollarSign => {
            Expression::Lambda(Box::new(Function::from_lambda(LambdaDecl::from(tokens)?)))
        }

        // Parenthesized expressions.
        TokenKind::LeftParen => {
            tokens.next();
            // TODO: Set the expression start and end positions to match
            // parenthesis.
            let expr = parse_expr(tokens)?;
            Module::parse_expecting(tokens, TokenKind::RightParen)?;
            expr
        }

        // Any expression that begins with `@` or an identifier.
        TokenKind::Identifier(_) | TokenKind::At => {
            let cursor_before_symbol = tokens.cursor();
            let symbol = Symbol::from(tokens)?;
            let cursor_after_symbol = tokens.cursor();

            match tokens.peek_next() {
                Some(Token {
                    kind: TokenKind::DoubleColon,
                    ..
                }) => {
                    tokens.set_cursor(cursor_before_symbol);
                    Expression::EnumInit(EnumVariantInit::from(tokens)?)
                }

                Some(Token {
                    kind: TokenKind::LeftBrace,
                    ..
                }) => {
                    // This might be struct initialization, or just part of a conditional that is
                    // followed by the conditional closure.
                    tokens.set_cursor(cursor_before_symbol);
                    if let Ok(struct_init) = StructInit::from(tokens) {
                        return Ok(Expression::StructInit(struct_init));
                    }

                    tokens.set_cursor(cursor_after_symbol);
                    Expression::Symbol(symbol)
                }

                _ => Expression::Symbol(symbol),
            }
        }

        // A `from` expression.
        TokenKind::From => Expression::From(From::from(tokens)?),

        other => {
            return Err(ParseError::new_with_token(
                ErrorKind::ExpectedExpr,
                format_code!("expected expression, but found {}", other).as_str(),
                token.clone(),
            ));
        }
    };

    Ok(expr)
}

#[cfg(test)]
mod tests {
    use crate::lexer::lex::lex;
    use crate::lexer::pos::{Position, Span};
    use crate::lexer::stream::Stream;
    use crate::lexer::token::Token;
    use crate::lexer::token_kind::TokenKind;
    use crate::parser::ast::bool_lit::BoolLit;
    use crate::parser::ast::expr::Expression;
    use crate::parser::ast::func_call::FuncCall;
    use crate::parser::ast::int_lit::IntLit;
    use crate::parser::ast::op::Operator;
    use crate::parser::ast::str_lit::StrLit;
    use crate::parser::ast::symbol::Symbol;
    use crate::parser::error::{ErrorKind, ParseError, ParseResult};

    fn parse(raw: &str) -> ParseResult<Expression> {
        let tokens = lex(raw).expect("should succeed");
        Expression::from(&mut Stream::from(tokens))
    }

    #[test]
    fn parse_basic_var_value() {
        assert_eq!(
            parse(r#"my_var"#).unwrap(),
            Expression::Symbol(Symbol {
                maybe_mod_name: None,
                name: "my_var".to_string(),
                params: vec![],
                span: Span {
                    start_pos: Position::new(1, 1),
                    end_pos: Position::new(1, 7),
                },
            })
        );
    }

    #[test]
    fn parse_basic_bool_literal() {
        assert_eq!(
            parse("true").unwrap(),
            Expression::BoolLiteral(BoolLit::new(
                true,
                Span {
                    start_pos: Position::new(1, 1),
                    end_pos: Position::new(1, 5)
                }
            ))
        );
        assert_eq!(
            parse("false").unwrap(),
            Expression::BoolLiteral(BoolLit::new(
                false,
                Span {
                    start_pos: Position::new(1, 1),
                    end_pos: Position::new(1, 6)
                },
            ))
        );
    }
    #[test]
    fn parse_basic_int_literal() {
        assert_eq!(
            parse("123").unwrap(),
            Expression::IntLiteral(IntLit {
                value: 123,
                has_suffix: false,
                span: Span {
                    start_pos: Position::new(1, 1),
                    end_pos: Position::new(1, 4),
                },
            })
        );
    }

    #[test]
    fn parse_basic_string_literal() {
        assert_eq!(
            parse(r#""this is my \"String\"""#).unwrap(),
            Expression::StrLiteral(StrLit {
                value: r#"this is my "String""#.to_string(),
                span: Span {
                    start_pos: Position::new(1, 1),
                    end_pos: Position::new(1, 24),
                },
            })
        );
    }

    #[test]
    fn parse_function_call() {
        assert_eq!(
            parse("call(3 * 2 - 2, other(!thing, 1 > var % 2))").unwrap(),
            Expression::FunctionCall(Box::new(FuncCall::new(
                Expression::Symbol(Symbol::new(
                    "call",
                    Span {
                        start_pos: Position::new(1, 1),
                        end_pos: Position::new(1, 5)
                    },
                )),
                vec![
                    Expression::BinaryOperation(
                        Box::new(Expression::BinaryOperation(
                            Box::new(Expression::IntLiteral(IntLit {
                                value: 3,
                                has_suffix: false,
                                span: Span {
                                    start_pos: Position::new(1, 6),
                                    end_pos: Position::new(1, 7),
                                },
                            })),
                            Operator::Multiply,
                            Box::new(Expression::IntLiteral(IntLit {
                                value: 2,
                                has_suffix: false,
                                span: Span {
                                    start_pos: Position::new(1, 10),
                                    end_pos: Position::new(1, 11),
                                },
                            }))
                        )),
                        Operator::Subtract,
                        Box::new(Expression::IntLiteral(IntLit {
                            value: 2,
                            has_suffix: false,
                            span: Span {
                                start_pos: Position::new(1, 14),
                                end_pos: Position::new(1, 15),
                            },
                        }))
                    ),
                    Expression::FunctionCall(Box::new(FuncCall::new(
                        Expression::Symbol(Symbol::new(
                            "other",
                            Span {
                                start_pos: Position::new(1, 17),
                                end_pos: Position::new(1, 22)
                            }
                        )),
                        vec![
                            Expression::UnaryOperation(
                                Operator::LogicalNot,
                                Box::new(Expression::Symbol(Symbol {
                                    maybe_mod_name: None,
                                    name: "thing".to_string(),
                                    params: vec![],
                                    span: Span {
                                        start_pos: Position::new(1, 24),
                                        end_pos: Position::new(1, 29),
                                    },
                                }))
                            ),
                            Expression::BinaryOperation(
                                Box::new(Expression::IntLiteral(IntLit {
                                    value: 1,
                                    has_suffix: false,
                                    span: Span {
                                        start_pos: Position::new(1, 31),
                                        end_pos: Position::new(1, 32),
                                    },
                                })),
                                Operator::GreaterThan,
                                Box::new(Expression::BinaryOperation(
                                    Box::new(Expression::Symbol(Symbol {
                                        maybe_mod_name: None,
                                        name: "var".to_string(),
                                        params: vec![],
                                        span: Span {
                                            start_pos: Position::new(1, 35),
                                            end_pos: Position::new(1, 38),
                                        },
                                    })),
                                    Operator::Modulo,
                                    Box::new(Expression::IntLiteral(IntLit {
                                        value: 2,
                                        has_suffix: false,
                                        span: Span {
                                            start_pos: Position::new(1, 41),
                                            end_pos: Position::new(1, 42),
                                        },
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
    fn parse_int_arithmetic() {
        assert_eq!(
            parse("(3 + 6) / 3 - 5 + 298 * 3").unwrap(),
            Expression::BinaryOperation(
                Box::new(Expression::BinaryOperation(
                    Box::new(Expression::BinaryOperation(
                        Box::new(Expression::BinaryOperation(
                            Box::new(Expression::IntLiteral(IntLit {
                                value: 3,
                                has_suffix: false,
                                span: Span {
                                    start_pos: Position::new(1, 2),
                                    end_pos: Position::new(1, 3),
                                },
                            })),
                            Operator::Add,
                            Box::new(Expression::IntLiteral(IntLit {
                                value: 6,
                                has_suffix: false,
                                span: Span {
                                    start_pos: Position::new(1, 6),
                                    end_pos: Position::new(1, 7),
                                },
                            }))
                        )),
                        Operator::Divide,
                        Box::new(Expression::IntLiteral(IntLit {
                            value: 3,
                            has_suffix: false,
                            span: Span {
                                start_pos: Position::new(1, 11),
                                end_pos: Position::new(1, 12),
                            },
                        }))
                    )),
                    Operator::Subtract,
                    Box::new(Expression::IntLiteral(IntLit {
                        value: 5,
                        has_suffix: false,
                        span: Span {
                            start_pos: Position::new(1, 15),
                            end_pos: Position::new(1, 16),
                        },
                    }))
                )),
                Operator::Add,
                Box::new(Expression::BinaryOperation(
                    Box::new(Expression::IntLiteral(IntLit {
                        value: 298,
                        has_suffix: false,
                        span: Span {
                            start_pos: Position::new(1, 19),
                            end_pos: Position::new(1, 22),
                        },
                    })),
                    Operator::Multiply,
                    Box::new(Expression::IntLiteral(IntLit {
                        value: 3,
                        has_suffix: false,
                        span: Span {
                            start_pos: Position::new(1, 25),
                            end_pos: Position::new(1, 26),
                        },
                    }))
                ))
            )
        )
    }

    #[test]
    fn parse_multiline_expr() {
        let raw = "(var - 3) / 4 * \n(call(true) % 2) + \n5";
        assert_eq!(
            parse(raw).unwrap(),
            Expression::BinaryOperation(
                Box::new(Expression::BinaryOperation(
                    Box::new(Expression::BinaryOperation(
                        Box::new(Expression::BinaryOperation(
                            Box::new(Expression::Symbol(Symbol {
                                maybe_mod_name: None,
                                name: "var".to_string(),
                                params: vec![],
                                span: Span {
                                    start_pos: Position::new(1, 2),
                                    end_pos: Position::new(1, 5),
                                },
                            })),
                            Operator::Subtract,
                            Box::new(Expression::IntLiteral(IntLit {
                                value: 3,
                                has_suffix: false,
                                span: Span {
                                    start_pos: Position::new(1, 8),
                                    end_pos: Position::new(1, 9)
                                },
                            })),
                        )),
                        Operator::Divide,
                        Box::new(Expression::IntLiteral(IntLit {
                            value: 4,
                            has_suffix: false,
                            span: Span {
                                start_pos: Position::new(1, 13),
                                end_pos: Position::new(1, 14)
                            },
                        })),
                    )),
                    Operator::Multiply,
                    Box::new(Expression::BinaryOperation(
                        Box::new(Expression::FunctionCall(Box::new(FuncCall::new(
                            Expression::Symbol(Symbol::new(
                                "call",
                                Span {
                                    start_pos: Position::new(2, 2),
                                    end_pos: Position::new(2, 6)
                                }
                            )),
                            vec![Expression::BoolLiteral(BoolLit {
                                value: true,
                                span: Span {
                                    start_pos: Position::new(2, 7),
                                    end_pos: Position::new(2, 11)
                                },
                            })],
                            Position::new(2, 12)
                        )))),
                        Operator::Modulo,
                        Box::new(Expression::IntLiteral(IntLit {
                            value: 2,
                            has_suffix: false,
                            span: Span {
                                start_pos: Position::new(2, 15),
                                end_pos: Position::new(2, 16)
                            },
                        })),
                    )),
                )),
                Operator::Add,
                Box::new(Expression::IntLiteral(IntLit {
                    value: 5,
                    has_suffix: false,
                    span: Span {
                        start_pos: Position::new(3, 1),
                        end_pos: Position::new(3, 2)
                    },
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
                    span: Span {
                        start_pos: Position { line: 1, col: 15 },
                        end_pos: Position { line: 1, col: 16 },
                    }
                }),
                span: Span {
                    start_pos: Position { line: 1, col: 15 },
                    end_pos: Position { line: 1, col: 16 },
                },
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
                        Box::new(Expression::IntLiteral(IntLit {
                            value: 8,
                            has_suffix: false,
                            span: Span {
                                start_pos: Position::new(1, 2),
                                end_pos: Position::new(1, 3),
                            },
                        })),
                    )),
                    Operator::Subtract,
                    Box::new(Expression::BinaryOperation(
                        Box::new(Expression::BinaryOperation(
                            Box::new(Expression::BinaryOperation(
                                Box::new(Expression::UnaryOperation(
                                    Operator::Subtract,
                                    Box::new(Expression::IntLiteral(IntLit {
                                        value: 100,
                                        has_suffix: false,
                                        span: Span {
                                            start_pos: Position::new(1, 8),
                                            end_pos: Position::new(1, 11),
                                        },
                                    }))
                                )),
                                Operator::Add,
                                Box::new(Expression::IntLiteral(IntLit {
                                    value: 2,
                                    has_suffix: false,
                                    span: Span {
                                        start_pos: Position::new(1, 14),
                                        end_pos: Position::new(1, 15)
                                    },
                                })),
                            )),
                            Operator::Multiply,
                            Box::new(Expression::IntLiteral(IntLit {
                                value: 4,
                                has_suffix: false,
                                span: Span {
                                    start_pos: Position::new(1, 19),
                                    end_pos: Position::new(1, 20)
                                },
                            })),
                        )),
                        Operator::Divide,
                        Box::new(Expression::IntLiteral(IntLit {
                            value: 2,
                            has_suffix: false,
                            span: Span {
                                start_pos: Position::new(1, 23),
                                end_pos: Position::new(1, 24)
                            },
                        })),
                    )),
                )),
                Operator::Add,
                Box::new(Expression::IntLiteral(IntLit {
                    value: 8,
                    has_suffix: false,
                    span: Span {
                        start_pos: Position::new(1, 27),
                        end_pos: Position::new(1, 28)
                    },
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
                Box::new(Expression::IntLiteral(IntLit {
                    value: 8,
                    has_suffix: false,
                    span: Span {
                        start_pos: Position::new(1, 2),
                        end_pos: Position::new(1, 3),
                    },
                })),
            )
        );

        let result = parse("-x").unwrap();
        assert_eq!(
            result,
            Expression::UnaryOperation(
                Operator::Subtract,
                Box::new(Expression::Symbol(Symbol {
                    maybe_mod_name: None,
                    name: "x".to_string(),
                    params: vec![],
                    span: Span {
                        start_pos: Position::new(1, 2),
                        end_pos: Position::new(1, 3),
                    },
                })),
            )
        );

        let result = parse("-f()").unwrap();
        assert_eq!(
            result,
            Expression::UnaryOperation(
                Operator::Subtract,
                Box::new(Expression::FunctionCall(Box::new(FuncCall::new(
                    Expression::Symbol(Symbol::new(
                        "f",
                        Span {
                            start_pos: Position::new(1, 2),
                            end_pos: Position::new(1, 3)
                        }
                    )),
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
                    Box::new(Expression::IntLiteral(IntLit {
                        value: 1,
                        has_suffix: false,
                        span: Span {
                            start_pos: Position::new(1, 4),
                            end_pos: Position::new(1, 5)
                        },
                    })),
                    Operator::GreaterThan,
                    Box::new(Expression::IntLiteral(IntLit {
                        value: 0,
                        has_suffix: false,
                        span: Span {
                            start_pos: Position::new(1, 6),
                            end_pos: Position::new(1, 7)
                        },
                    })),
                )),
                Operator::Add,
                Box::new(Expression::IntLiteral(IntLit {
                    value: 1,
                    has_suffix: false,
                    span: Span {
                        start_pos: Position::new(1, 9),
                        end_pos: Position::new(1, 10)
                    },
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
                                        maybe_mod_name: None,
                                        name: "v".to_string(),
                                        params: vec![],
                                        span: Span {
                                            start_pos: Position { line: 1, col: 5 },
                                            end_pos: Position { line: 1, col: 6 },
                                        },
                                    }))
                                )),
                                Operator::Subtract,
                                Box::new(Expression::UnaryOperation(
                                    Operator::Subtract,
                                    Box::new(Expression::Symbol(Symbol {
                                        maybe_mod_name: None,
                                        name: "a".to_string(),
                                        params: vec![],
                                        span: Span {
                                            start_pos: Position { line: 1, col: 8 },
                                            end_pos: Position { line: 1, col: 9 },
                                        },
                                    }))
                                )),
                            )),
                        )),
                    )),
                    Operator::Subtract,
                    Box::new(Expression::IntLiteral(IntLit {
                        value: 2,
                        has_suffix: false,
                        span: Span {
                            start_pos: Position { line: 1, col: 11 },
                            end_pos: Position { line: 1, col: 12 },
                        },
                    })),
                )),
                Operator::Subtract,
                Box::new(Expression::UnaryOperation(
                    Operator::Subtract,
                    Box::new(Expression::BinaryOperation(
                        Box::new(Expression::UnaryOperation(
                            Operator::Subtract,
                            Box::new(Expression::IntLiteral(IntLit {
                                value: 100,
                                has_suffix: false,
                                span: Span {
                                    start_pos: Position { line: 1, col: 16 },
                                    end_pos: Position { line: 1, col: 19 },
                                },
                            })),
                        )),
                        Operator::Subtract,
                        Box::new(Expression::UnaryOperation(
                            Operator::Subtract,
                            Box::new(Expression::FunctionCall(Box::new(FuncCall {
                                fn_expr: Expression::Symbol(Symbol {
                                    maybe_mod_name: None,
                                    name: "call".to_string(),
                                    params: vec![],
                                    span: Span {
                                        start_pos: Position { line: 1, col: 23 },
                                        end_pos: Position { line: 1, col: 27 },
                                    },
                                },),
                                args: vec![Expression::IntLiteral(IntLit {
                                    value: 1,
                                    has_suffix: false,
                                    span: Span {
                                        start_pos: Position { line: 1, col: 28 },
                                        end_pos: Position { line: 1, col: 29 },
                                    },
                                })],
                                span: Span {
                                    start_pos: Position { line: 1, col: 23 },
                                    end_pos: Position { line: 1, col: 30 },
                                },
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
                            maybe_mod_name: None,
                            name: "b".to_string(),
                            params: vec![],
                            span: Span {
                                start_pos: Position::new(1, 4),
                                end_pos: Position::new(1, 5),
                            },
                        })),
                    )),
                    Operator::Subtract,
                    Box::new(Expression::UnaryOperation(
                        Operator::Subtract,
                        Box::new(Expression::IntLiteral(IntLit {
                            value: 100,
                            has_suffix: false,
                            span: Span {
                                start_pos: Position::new(1, 8),
                                end_pos: Position::new(1, 11),
                            },
                        })),
                    )),
                )),
            )
        )
    }

    #[test]
    fn parse_multiline_string() {
        let string = r#""this
            is a string
            that runs
            multiple
            lines!
        ""#;
        let result = parse(string).unwrap();
        assert_eq!(
            result,
            Expression::StrLiteral(StrLit {
                value: string.replace('"', ""),
                span: Span {
                    start_pos: Position::new(1, 1),
                    end_pos: Position::new(6, 9),
                },
            })
        )
    }

    #[test]
    fn unclosed_str_lit() {
        let result = lex(r#"
            fn main() {
                let a = "        ayyy
            }"#);
        assert!(matches!(result, Err(_)));
    }
}
