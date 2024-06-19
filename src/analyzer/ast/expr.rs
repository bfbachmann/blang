use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::ast::array::AArrayInit;
use crate::analyzer::ast::closure::{check_closure_returns, check_closure_yields, AClosure};
use crate::analyzer::ast::fn_call::AFnCall;
use crate::analyzer::ast::func::{AFn, AFnSig};
use crate::analyzer::ast::index::AIndex;
use crate::analyzer::ast::member::AMemberAccess;
use crate::analyzer::ast::pointer::APointerType;
use crate::analyzer::ast::r#enum::AEnumVariantInit;
use crate::analyzer::ast::r#struct::AStructInit;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::statement::AStatement;
use crate::analyzer::ast::symbol::ASymbol;
use crate::analyzer::ast::tuple::ATupleInit;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::{Scope, ScopeKind};
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::{Locatable, Position, Span};
use crate::parser::ast::array::ArrayInit;
use crate::parser::ast::expr::Expression;
use crate::parser::ast::from::From;
use crate::parser::ast::func::Function;
use crate::parser::ast::func_call::FuncCall;
use crate::parser::ast::op::Operator;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::symbol::Symbol;
use crate::parser::ast::tuple::TupleInit;
use crate::parser::ast::unresolved::UnresolvedType;
use crate::{format_code, locatable_impl};

/// Represents a kind of expression.
#[derive(Debug, Clone)]
pub enum AExprKind {
    Symbol(ASymbol),
    MemberAccess(Box<AMemberAccess>),
    BoolLiteral(bool),
    I8Literal(i8),
    U8Literal(u8),
    I32Literal(i32),
    U32Literal(u32),
    F32Literal(f32),
    I64Literal(i64),
    U64Literal(u64),
    F64Literal(f64, bool),
    IntLiteral(i64, bool),
    UintLiteral(u64),
    StrLiteral(String),
    StructInit(AStructInit),
    EnumInit(AEnumVariantInit),
    TupleInit(ATupleInit),
    ArrayInit(AArrayInit),
    Index(Box<AIndex>),
    FunctionCall(Box<AFnCall>),
    AnonFunction(Box<AFn>),
    UnaryOperation(Operator, Box<AExpr>),
    BinaryOperation(Box<AExpr>, Operator, Box<AExpr>),
    TypeCast(Box<AExpr>, TypeKey),
    Sizeof(TypeKey),
    From(Box<AStatement>),
    Unknown,
}

impl fmt::Display for AExprKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            AExprKind::Symbol(sym) => write!(f, "{}", sym),
            AExprKind::MemberAccess(m) => write!(f, "{}", m),
            AExprKind::BoolLiteral(b) => write!(f, "{}", b),
            AExprKind::I8Literal(i) => write!(f, "{}i8", i),
            AExprKind::U8Literal(i) => write!(f, "{}u8", i),
            AExprKind::I32Literal(i) => write!(f, "{}i32", i),
            AExprKind::U32Literal(i) => write!(f, "{}u32", i),
            AExprKind::F32Literal(i) => write!(f, "{}f32", i),
            AExprKind::I64Literal(i) => write!(f, "{}i64", i),
            AExprKind::U64Literal(i) => write!(f, "{}u64", i),
            AExprKind::F64Literal(i, has_suffix) => write!(
                f,
                "{}{}",
                i,
                match has_suffix {
                    true => "f64",
                    false => "",
                }
            ),
            AExprKind::IntLiteral(i, has_suffix) => write!(
                f,
                "{}{}",
                i,
                match has_suffix {
                    true => "int",
                    false => "",
                }
            ),
            AExprKind::UintLiteral(i) => write!(f, "{}", i),
            AExprKind::StrLiteral(s) => write!(f, "{}", s),
            AExprKind::StructInit(s) => write!(f, "{}", s),
            AExprKind::EnumInit(e) => write!(f, "{}", e),
            AExprKind::TupleInit(t) => write!(f, "{}", t),
            AExprKind::ArrayInit(a) => write!(f, "{}", a),
            AExprKind::Index(i) => write!(f, "{}", i),
            AExprKind::FunctionCall(call) => write!(f, "{}", call),
            AExprKind::AnonFunction(func) => write!(f, "{}", *func),
            AExprKind::UnaryOperation(op, expr) => match op {
                Operator::Defererence => write!(f, "{}{}", expr, op),
                Operator::MutReference => write!(f, "{} {}", op, expr),
                _ => write!(f, "{}{}", op, expr),
            },
            AExprKind::BinaryOperation(left, op, right) => {
                write!(f, "{} {} {}", left, op, right)
            }
            AExprKind::TypeCast(expr, target_type_key) => {
                write!(f, "{} as {}", expr, target_type_key)
            }
            AExprKind::Sizeof(type_key) => {
                write!(f, "sizeof {}", type_key)
            }
            AExprKind::From(statement) => {
                write!(f, "from {}", statement)
            }
            AExprKind::Unknown => {
                write!(f, "<unknown>")
            }
        }
    }
}

impl PartialEq for AExprKind {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (AExprKind::Symbol(v1), AExprKind::Symbol(v2)) => v1 == v2,
            (AExprKind::BoolLiteral(b1), AExprKind::BoolLiteral(b2)) => b1 == b2,
            (AExprKind::I64Literal(i1), AExprKind::I64Literal(i2)) => i1 == i2,
            (AExprKind::U64Literal(i1), AExprKind::U64Literal(i2)) => i1 == i2,
            (AExprKind::IntLiteral(i1, _), AExprKind::IntLiteral(i2, _)) => i1 == i2,
            (AExprKind::UintLiteral(i1), AExprKind::UintLiteral(i2)) => i1 == i2,
            (AExprKind::StrLiteral(s1), AExprKind::StrLiteral(s2)) => s1 == s2,
            (AExprKind::StructInit(s1), AExprKind::StructInit(s2)) => s1 == s2,
            (AExprKind::EnumInit(e1), AExprKind::EnumInit(e2)) => e1 == e2,
            (AExprKind::TupleInit(t1), AExprKind::TupleInit(t2)) => t1 == t2,
            (AExprKind::ArrayInit(a1), AExprKind::ArrayInit(a2)) => a1 == a2,
            (AExprKind::FunctionCall(f1), AExprKind::FunctionCall(f2)) => f1 == f2,
            (AExprKind::AnonFunction(a1), AExprKind::AnonFunction(a2)) => a1 == a2,
            (AExprKind::UnaryOperation(o1, e1), AExprKind::UnaryOperation(o2, e2)) => {
                o1 == o2 && e1 == e2
            }
            (AExprKind::BinaryOperation(l1, o1, r1), AExprKind::BinaryOperation(l2, o2, r2)) => {
                l1 == l2 && o1 == o2 && r1 == r2
            }
            (AExprKind::Sizeof(tk1), AExprKind::Sizeof(tk2)) => tk1 == tk2,
            (AExprKind::From(s1), AExprKind::From(s2)) => s1 == s2,
            (AExprKind::Unknown, AExprKind::Unknown) => true,
            (_, _) => false,
        }
    }
}

impl AExprKind {
    /// Returns true if the expression is a symbol representing a type.
    pub fn is_type(&self) -> bool {
        match self {
            AExprKind::Symbol(symbol) if symbol.is_type => true,
            _ => false,
        }
    }

    /// Returns true if the expression kind can be used as a constant.
    pub fn is_const(&self) -> bool {
        match self {
            // Primitive literals are valid constants.
            AExprKind::BoolLiteral(_)
            | AExprKind::I8Literal(_)
            | AExprKind::U8Literal(_)
            | AExprKind::I32Literal(_)
            | AExprKind::U32Literal(_)
            | AExprKind::F32Literal(_)
            | AExprKind::I64Literal(_)
            | AExprKind::U64Literal(_)
            | AExprKind::F64Literal(_, _)
            | AExprKind::IntLiteral(_, _)
            | AExprKind::UintLiteral(_)
            | AExprKind::StrLiteral(_) => true,

            // Unary and binary operations are constants if they only operate on constants and have
            // valid constant operators.
            AExprKind::UnaryOperation(op, expr) => expr.kind.is_const() && op.is_const(),
            AExprKind::BinaryOperation(left_expr, op, right_expr) => {
                left_expr.kind.is_const() && right_expr.kind.is_const() && op.is_const()
            }

            // Struct initializations are constants if all their fields are constants.
            AExprKind::StructInit(struct_init) => {
                for (_, field_val) in &struct_init.field_values {
                    if !field_val.kind.is_const() {
                        return false;
                    }
                }

                true
            }

            // Enum variant initializations are constants if they have no values or their values
            // are constants.
            AExprKind::EnumInit(enum_init) => {
                if let Some(val) = &enum_init.maybe_value {
                    if !val.kind.is_const() {
                        return false;
                    }
                }

                true
            }

            // Tuple values are constants if all their fields are constants.
            AExprKind::TupleInit(tuple_init) => {
                for val in &tuple_init.values {
                    if !val.kind.is_const() {
                        return false;
                    }
                }

                true
            }

            // Array values are constants if all their fields are constants.
            AExprKind::ArrayInit(array_init) => {
                for val in &array_init.values {
                    if !val.kind.is_const() {
                        return false;
                    }
                }

                true
            }

            // Array index expressions are never constant. This is mostly for
            // simplicity.
            AExprKind::Index(_) => false,

            // Symbols can be constants.
            AExprKind::Symbol(sym) => sym.is_const,

            // Function calls and unknown values are never constants.
            AExprKind::FunctionCall(_) | AExprKind::AnonFunction(_) | AExprKind::Unknown => false,

            // Type cast expressions are constants if the expressions they're type casting are
            // constants.
            AExprKind::TypeCast(expr, _) => expr.kind.is_const(),

            // Member access expressions are constants if their parent values are constants.
            AExprKind::MemberAccess(access) => access.base_expr.kind.is_const(),

            // `sizeof` expressions always yield a constant value.
            AExprKind::Sizeof(_) => true,

            // `from` expressions are never considered constant. Maybe this should
            // be reconsidered in the future, since they could actually be constant
            // in some cases.
            AExprKind::From(_) => false,
        }
    }

    /// Returns the human-readable version of this expression kind.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        match self {
            AExprKind::Symbol(sym) => format!("{}", sym),
            AExprKind::BoolLiteral(b) => format!("{}", b),
            AExprKind::I8Literal(i) => format!("{}", i),
            AExprKind::U8Literal(i) => format!("{}", i),
            AExprKind::I32Literal(i) => format!("{}", i),
            AExprKind::U32Literal(i) => format!("{}", i),
            AExprKind::F32Literal(i) => format!("{}", i),
            AExprKind::I64Literal(i) => format!("{}", i),
            AExprKind::U64Literal(i) => format!("{}", i),
            AExprKind::F64Literal(i, has_suffix) => format!(
                "{}{}",
                i,
                match has_suffix {
                    true => "f64",
                    false => "",
                }
            ),
            AExprKind::IntLiteral(i, has_suffix) => format!(
                "{}{}",
                i,
                match has_suffix {
                    true => "int",
                    false => "",
                }
            ),
            AExprKind::UintLiteral(i) => format!("{}", i),
            AExprKind::StrLiteral(s) => format!("{}", s),
            AExprKind::StructInit(s) => s.display(ctx),
            AExprKind::EnumInit(e) => e.display(ctx),
            AExprKind::TupleInit(t) => t.display(ctx),
            AExprKind::ArrayInit(a) => a.display(ctx),
            AExprKind::Index(i) => i.display(ctx),
            AExprKind::FunctionCall(call) => call.display(ctx),
            AExprKind::AnonFunction(func) => func.display(ctx),
            AExprKind::UnaryOperation(op, expr) => match op {
                Operator::Defererence => format!("{}{}", expr.display(ctx), op),
                Operator::MutReference => format!("{} {}", op, expr.display(ctx)),
                _ => format!("{}{}", op, expr.display(ctx)),
            },
            AExprKind::BinaryOperation(left, op, right) => {
                format!("{} {} {}", left.display(ctx), op, right.display(ctx))
            }
            AExprKind::TypeCast(left_expr, target_type_key) => {
                format!(
                    "{} as {}",
                    left_expr.display(ctx),
                    ctx.display_type_for_key(*target_type_key)
                )
            }
            AExprKind::Sizeof(type_key) => {
                format!("sizeof {}", ctx.display_type_for_key(*type_key))
            }
            AExprKind::MemberAccess(access) => {
                format!("{}.{}", access.base_expr.display(ctx), access.member_name)
            }
            AExprKind::From(statement) => {
                format!("from {}", statement)
            }
            AExprKind::Unknown => "<unknown>".to_string(),
        }
    }
}

/// Represents a semantically valid and type-rich expression.
#[derive(Clone, PartialEq, Debug)]
pub struct AExpr {
    pub kind: AExprKind,
    pub type_key: TypeKey,
    span: Span,
}

impl fmt::Display for AExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind)
    }
}

locatable_impl!(AExpr);

impl AExpr {
    /// Creates a new expression.
    pub fn new(kind: AExprKind, type_key: TypeKey, span: Span) -> AExpr {
        AExpr {
            kind,
            type_key,
            span,
        }
    }

    /// Performs semantic analysis on the given expression and returns a type-rich version of it.
    /// `maybe_expected_type_key` is the optional type key of the expected type that this expression
    /// should have.
    /// If `allow_type` is true and the expression is a symbol, the symbol may refer to a type instead
    /// of a value. Otherwise, if the expression is a symbol that refers to a type, an error will be
    /// raised.
    /// If `ignore_mutability` is true, the mutability of pointer types will not be taken into
    /// account when checking and coercing types.
    pub fn from(
        ctx: &mut ProgramContext,
        expr: Expression,
        maybe_expected_type_key: Option<TypeKey>,
        allow_type: bool,
        ignore_mutability: bool,
    ) -> AExpr {
        AExpr::from_with_pref(
            ctx,
            expr,
            maybe_expected_type_key,
            allow_type,
            ignore_mutability,
            false,
        )
    }

    /// Does the same thing as `from`, but allows the caller to specify how to resolve ambiguous
    /// member accesses based on whether the caller prefers a method or a field. This is only really
    /// relevant to struct types with field names that match their method names.
    pub fn from_with_pref(
        ctx: &mut ProgramContext,
        expr: Expression,
        maybe_expected_type_key: Option<TypeKey>,
        allow_type: bool,
        ignore_mutability: bool,
        prefer_method: bool,
    ) -> AExpr {
        let result = analyze_expr_with_pref(
            ctx,
            expr.clone(),
            maybe_expected_type_key,
            allow_type,
            prefer_method,
            Span {
                start_pos: expr.start_pos().clone(),
                end_pos: expr.end_pos().clone(),
            },
        );

        // Try to (safely) coerce the expression to the right type (this may involve generic
        // rendering).
        result.coerce_and_check_types(ctx, maybe_expected_type_key, &expr, ignore_mutability)
    }

    /// Returns a string containing the human-readable version of this expression.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        self.kind.display(ctx)
    }

    /// Checks if type coercion to the expected type is necessary and, if so, attempts it before
    /// performing type checks. Adds an error to the program context if type checks fail. No
    /// type checks are performed if `maybe_expected_type_key` is None.
    /// If `ignore_mutability` is true, the mutability of pointer types will not be taken into
    /// account when checking and coercing types.
    fn coerce_and_check_types(
        mut self,
        ctx: &mut ProgramContext,
        maybe_expected_type_key: Option<TypeKey>,
        expr: &Expression,
        ignore_mutability: bool,
    ) -> Self {
        let expected_tk = match maybe_expected_type_key {
            Some(tk) => tk,
            None => return self,
        };

        // Try to coerce this expression to the expected type before doing the type check.
        self = self.try_coerce_to(ctx, expected_tk);

        // Skip the type check if either type is unknown, as this implies that semantic analysis
        // has already failed somewhere else in this expression or wherever it's being used.
        let actual_type = ctx.must_get_type(self.type_key);
        let expected_type = ctx.must_get_type(expected_tk);
        if actual_type.is_unknown() || expected_type.is_unknown() {
            return self;
        }

        if !actual_type.is_same_as(ctx, &expected_type, ignore_mutability) {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::MismatchedTypes,
                format_code!(
                    "expected expression of type {}, but found {}",
                    expected_type.display(ctx),
                    actual_type.display(ctx),
                )
                .as_str(),
                expr,
            ));
        }

        self
    }

    /// Checks that this expression represents a value can be referenced as mutable
    /// (i.e. we can take a `&mut` to it). Inserts an error into the program context if not.
    pub fn check_referencable_as_mut<T: Locatable>(&self, ctx: &mut ProgramContext, loc: &T) {
        // Make sure the expression is mutable if it comes from a variable. If it generates
        // some brand-new value, then it can trivially be considered mutable.
        let symbol = match self.get_base_symbol() {
            Some(symbol) => symbol,
            None => return,
        };

        let scoped_symbol = match ctx.get_scoped_symbol(None, symbol.name.as_str()) {
            Some(scoped_symbol) => scoped_symbol,
            None => return,
        };

        if scoped_symbol.is_const {
            ctx.insert_err(
                AnalyzeError::new(
                    ErrorKind::InvalidMutRef,
                    format_code!("cannot get mutating pointer to constant value {}", symbol)
                        .as_str(),
                    loc,
                )
                .with_help(
                    format_code!("Consider declaring {} as a mutable local variable.", symbol)
                        .as_str(),
                ),
            );
        } else if !scoped_symbol.is_mut
            && !ctx.must_get_type(scoped_symbol.type_key).is_mut_pointer()
        {
            ctx.insert_err(
                AnalyzeError::new(
                    ErrorKind::InvalidMutRef,
                    format_code!("cannot get mutating pointer to immutable value {}", symbol)
                        .as_str(),
                    loc,
                )
                .with_help(format_code!("Consider declaring {} as mutable.", symbol).as_str()),
            );
        }
    }

    /// Tries to coerce this expression to the target type. If coercion is successful, returns
    /// the coerced expression, otherwise just returns the expression as-is.
    pub fn try_coerce_to(mut self, ctx: &mut ProgramContext, target_type_key: TypeKey) -> Self {
        let target_type = ctx.must_get_type(target_type_key);
        if target_type.is_unknown() {
            return self;
        }

        // If both types are pointers, make sure their pointee types are the same
        // and immutability is not violated. If so, we can allow coercion.
        if let (AType::Pointer(self_ptr_type), AType::Pointer(other_ptr_type)) =
            (ctx.must_get_type(self.type_key), target_type)
        {
            let pointee_type_match =
                self_ptr_type.pointee_type_key == other_ptr_type.pointee_type_key;
            let immutability_intact = self_ptr_type.is_mut || !other_ptr_type.is_mut;
            if pointee_type_match && immutability_intact {
                self.type_key = target_type_key;
                return self;
            }
        }

        match &self.kind {
            // Only allow coercion of `int` literals if they don't have explicit type suffixes.
            AExprKind::IntLiteral(i, false) if *i >= 0 => match target_type {
                AType::Uint => {
                    self.kind = AExprKind::UintLiteral(*i as u64);
                    self.type_key = ctx.uint_type_key();
                }

                AType::I64 => {
                    self.kind = AExprKind::I64Literal(*i);
                    self.type_key = ctx.i64_type_key();
                }

                AType::U64 => {
                    self.kind = AExprKind::U64Literal(*i as u64);
                    self.type_key = ctx.u64_type_key();
                }

                AType::U32 => {
                    if *i > u32::MAX as i64 {
                        ctx.insert_err(AnalyzeError::new(
                            ErrorKind::LiteralOutOfRange,
                            format_code!("literal out of range for {}", "u32").as_str(),
                            &self,
                        ));
                    }

                    self.kind = AExprKind::U32Literal(*i as u32);
                    self.type_key = ctx.u32_type_key();
                }

                AType::U8 => {
                    if *i > u8::MAX as i64 {
                        ctx.insert_err(AnalyzeError::new(
                            ErrorKind::LiteralOutOfRange,
                            format_code!("literal out of range for {}", "u8").as_str(),
                            &self,
                        ));
                    }

                    self.kind = AExprKind::U8Literal(*i as u8);
                    self.type_key = ctx.u8_type_key();
                }

                AType::I32 => {
                    if *i > i32::MAX as i64 {
                        ctx.insert_err(AnalyzeError::new(
                            ErrorKind::LiteralOutOfRange,
                            format_code!("literal out of range for {}", "i32").as_str(),
                            &self,
                        ));
                    }

                    self.kind = AExprKind::I32Literal(*i as i32);
                    self.type_key = ctx.i32_type_key();
                }

                AType::I8 => {
                    if *i > i8::MAX as i64 {
                        ctx.insert_err(AnalyzeError::new(
                            ErrorKind::LiteralOutOfRange,
                            format_code!("literal out of range for {}", "i8").as_str(),
                            &self,
                        ));
                    }

                    self.kind = AExprKind::I8Literal(*i as i8);
                    self.type_key = ctx.i8_type_key();
                }
                _ => {}
            },

            // Only allow coercion of `f64` literals if they don't have explicit type suffixes.
            AExprKind::F64Literal(f, false) => match target_type {
                AType::F32 => {
                    if *f > f32::MAX as f64 || *f < f32::MIN as f64 {
                        ctx.insert_err(AnalyzeError::new(
                            ErrorKind::LiteralOutOfRange,
                            format_code!("literal out of range for {}", "f32").as_str(),
                            &self,
                        ));
                    }

                    self.kind = AExprKind::F32Literal(*f as f32);
                    self.type_key = ctx.f32_type_key();
                }
                _ => {}
            },

            // Only allow coercion of negated values if the target type is signed.
            AExprKind::UnaryOperation(Operator::Subtract, operand) if target_type.is_signed() => {
                let new_operand = operand.clone().try_coerce_to(ctx, target_type_key);
                self.type_key = new_operand.type_key;
                self.kind = AExprKind::UnaryOperation(Operator::Subtract, Box::new(new_operand));
            }

            AExprKind::Symbol(symbol) => {
                // Always coerce `null` to any pointer type.
                if symbol.is_null_intrinsic() && target_type.is_ptr() {
                    self.type_key = target_type_key;
                    self.kind = AExprKind::Symbol(ASymbol::new_null(
                        ctx,
                        Some(target_type_key),
                        symbol.span().clone(),
                    ));
                    return self;
                }

                match ctx.must_get_type(symbol.type_key) {
                    AType::Function(sig) if sig.is_parameterized() => {
                        todo!()
                    }
                    _ => return self,
                };
            }

            _ => {}
        };

        self
    }

    /// Creates a new expression.
    pub fn new_with_default_pos(kind: AExprKind, type_key: TypeKey) -> Self {
        AExpr {
            kind,
            type_key,
            span: Default::default(),
        }
    }

    /// Returns a new expression with value null. The null value for pointer types is just 0u64
    /// type cast to that type.
    pub fn new_null_ptr(ctx: &mut ProgramContext, maybe_type_key: Option<TypeKey>) -> AExpr {
        let null_symbol = ASymbol::new_null(ctx, maybe_type_key, Default::default());
        AExpr {
            type_key: null_symbol.type_key,
            kind: AExprKind::Symbol(null_symbol),
            span: Default::default(),
        }
    }

    /// Creates a new zero-valued expression of the given type.
    pub fn new_zero_value(ctx: &mut ProgramContext, typ: Type) -> Self {
        let type_key = ctx.resolve_type(&typ);
        let span = typ.span().clone();

        match typ {
            Type::Tuple(_) => AExpr {
                kind: AExprKind::TupleInit(ATupleInit::new_empty(ctx)),
                type_key,
                span,
            },

            Type::Array(_) => AExpr {
                kind: AExprKind::ArrayInit(AArrayInit::new_empty(ctx)),
                type_key,
                span,
            },

            Type::Function(_) => AExpr {
                kind: AExprKind::AnonFunction(Box::new(AFn {
                    signature: AFnSig {
                        name: "".to_string(),
                        mangled_name: "".to_string(),
                        args: vec![],
                        maybe_ret_type_key: None,
                        type_key,
                        maybe_impl_type_key: None,
                        params: None,
                    },
                    body: AClosure::new_empty(),
                })),
                type_key,
                span,
            },

            Type::Unresolved(unresolved_type) => {
                let kind = match unresolved_type.name.as_str() {
                    "bool" => AExprKind::BoolLiteral(false),
                    "i8" => AExprKind::I8Literal(0),
                    "u8" => AExprKind::U8Literal(0),
                    "i32" => AExprKind::I32Literal(0),
                    "u32" => AExprKind::U32Literal(0),
                    "i64" => AExprKind::I64Literal(0),
                    "u64" => AExprKind::U64Literal(0),
                    "int" => AExprKind::IntLiteral(0, false),
                    "uint" => AExprKind::UintLiteral(0),
                    "str" => AExprKind::StrLiteral("".to_string()),
                    _ => AExprKind::Unknown,
                };

                AExpr {
                    kind,
                    type_key,
                    span,
                }
            }

            Type::Pointer(_) => AExpr::new_null_ptr(ctx, None),
        }
    }

    /// Tries to compute the value of this expression as a `uint`. Returns `None` if
    /// this expression does not result in a constant `uint` value.
    pub fn try_into_const_uint(&self, ctx: &mut ProgramContext) -> Option<u64> {
        let expr = self.clone().try_coerce_to(ctx, ctx.uint_type_key());

        if !expr.kind.is_const()
            || !ctx
                .must_get_type(expr.type_key)
                .is_same_as(ctx, &AType::Uint, true)
        {
            return None;
        }

        return match &expr.kind {
            AExprKind::Symbol(symbol) => {
                let const_value = ctx.get_const_value(symbol.name.as_str()).unwrap().clone();
                const_value.try_into_const_uint(ctx)
            }

            AExprKind::IntLiteral(i, false) => {
                if *i < 0 {
                    None
                } else {
                    Some(*i as u64)
                }
            }

            AExprKind::UintLiteral(u) => Some(*u),

            AExprKind::BinaryOperation(left_expr, op, right_expr) => {
                let left = left_expr.try_into_const_uint(ctx).unwrap();
                let right = right_expr.try_into_const_uint(ctx).unwrap();
                match op {
                    Operator::Add => Some(left + right),
                    Operator::Subtract => Some(left - right),
                    Operator::Multiply => Some(left * right),
                    Operator::Divide => Some(left / right),
                    Operator::Modulo => Some(left % right),
                    other => panic!("unexpected operator {}", other),
                }
            }

            AExprKind::TypeCast(expr, target_type_key) => {
                // At this point we already know that the expression can be cast to u64 because
                // we checked its type above.
                let mut expr = expr.clone();
                expr.type_key = *target_type_key;
                return expr.try_into_const_uint(ctx);
            }

            _ => None,
        };
    }

    /// Locates and returns the symbol at the base of this expression. This will return `None` for all expressions
    /// other than symbols and member accesses that have symbols at their base.
    pub fn get_base_symbol(&self) -> Option<&ASymbol> {
        match &self.kind {
            AExprKind::Symbol(s) => Some(s),
            AExprKind::MemberAccess(access) => access.get_base_expr().get_base_symbol(),
            AExprKind::Index(index) => index.collection_expr.get_base_symbol(),
            AExprKind::UnaryOperation(Operator::Defererence, operand) => operand.get_base_symbol(),
            _ => None,
        }
    }
}

/// Checks that the operands of a binary operation are compatible with the operator and one
/// another. If successful, returns the type key of the operands (their types should be the
/// same).
fn check_operand_types(
    ctx: &ProgramContext,
    left_expr: &AExpr,
    op: &Operator,
    right_expr: &AExpr,
) -> Result<Option<TypeKey>, Vec<AnalyzeError>> {
    let left_type = ctx.must_get_type(left_expr.type_key);
    let right_type = ctx.must_get_type(right_expr.type_key);

    let mut left_type_key = None;
    let mut right_type_key = None;
    let mut errors = vec![];

    if !is_valid_operand_type(op, left_type, true) {
        errors.push(AnalyzeError::new(
            ErrorKind::MismatchedTypes,
            format_code!(
                "cannot apply operator {} to left-side expression of type {}",
                &op,
                ctx.display_type_for_key(left_expr.type_key),
            )
            .as_str(),
            left_expr,
        ));
    } else {
        left_type_key = Some(left_expr.type_key);
    }

    if !is_valid_operand_type(op, right_type, false) {
        errors.push(AnalyzeError::new(
            ErrorKind::MismatchedTypes,
            format_code!(
                "cannot apply operator {} to right-side expression of type {}",
                &op,
                ctx.display_type_for_key(right_expr.type_key),
            )
            .as_str(),
            right_expr,
        ));
    } else {
        right_type_key = Some(right_expr.type_key);
    }

    // Operands need to be the same in all cases except for bit shift operations.
    if !op.is_bitshift() && !right_type.is_same_as(ctx, left_type, true) {
        errors.push(AnalyzeError::new(
            ErrorKind::MismatchedTypes,
            format_code!(
                "{} operands have mismatched types {} and {}",
                op,
                left_type.display(ctx),
                right_type.display(ctx),
            )
            .as_str(),
            right_expr,
        ));
    }

    // Determine the result type from whichever operand type isn't None.
    let maybe_result_tk = match (left_type_key, right_type_key) {
        (Some(ltk), Some(rtk)) => {
            // In the case of pointer arithmetic, if either of the pointers is
            // mutable, we'll make the result mutable as well.
            if ctx.must_get_type(rtk).is_mut_pointer() {
                Some(rtk)
            } else {
                Some(ltk)
            }
        }
        (Some(ltk), _) => Some(ltk),
        (_, Some(rtk)) => Some(rtk),
        _ => None,
    };

    match errors.is_empty() {
        true => Ok(maybe_result_tk),
        false => Err(errors),
    }
}

/// Returns true only if `operand_type` is valid for operator `op`.
fn is_valid_operand_type(op: &Operator, operand_type: &AType, is_left_operand: bool) -> bool {
    // Determine the expected operand types on the operator.
    match op {
        // Mathematical operators only work on numeric and pointer types.
        Operator::Add
        | Operator::Subtract
        | Operator::Multiply
        | Operator::Divide
        | Operator::Modulo => operand_type.is_numeric() || operand_type.is_ptr(),

        // Logical operators only work on bools.
        Operator::LogicalAnd | Operator::LogicalOr => operand_type == &AType::Bool,

        // Bitwise `band` and `bor` operators only work on integers.
        Operator::BitwiseAnd | Operator::BitwiseOr => operand_type.is_integer(),

        // Bit shift operators take integers as their left operands and unsigned integers as
        // their right operands.
        Operator::BitwiseLeftShift | Operator::BitwiseRightShift => match is_left_operand {
            true => operand_type.is_integer(),
            false => operand_type.is_integer() && !operand_type.is_signed(),
        },

        // Bitwise xor works on bools and integers.
        Operator::BitwiseXor => operand_type.is_integer() || operand_type == &AType::Bool,

        // Equality operators work on most primitive types.
        Operator::EqualTo | Operator::NotEqualTo => {
            operand_type.is_numeric()
                || operand_type.is_ptr()
                || matches!(operand_type, AType::Bool | AType::Str)
        }

        // Both operands of "like" and "not like" comparisons should be enums.
        Operator::Like | Operator::NotLike => matches!(operand_type, AType::Enum(_)),

        // Comparators work on numeric and pointer types.
        Operator::GreaterThan
        | Operator::LessThan
        | Operator::GreaterThanOrEqual
        | Operator::LessThanOrEqual => operand_type.is_numeric() || operand_type.is_ptr(),

        // If this happens, something is badly broken.
        other => panic!("unexpected operator {}", other),
    }
}

/// Returns true only if it is possible to cast from `left_type` to `right_type`.
fn is_valid_type_cast(left_type: &AType, right_type: &AType) -> bool {
    match (left_type, right_type) {
        // Casting between numeric types is allowed.
        (a, b) if a.is_numeric() && b.is_numeric() => true,

        // Casting between pointer types is allowed as long as immutability isn't broken.
        (AType::Pointer(p1), AType::Pointer(p2)) => p1.is_mut || !p2.is_mut,

        // Casting between numeric types and pointers is allowed so long as
        // immutability is not violated.
        // Casting `str` to `*u8` is also allowed.
        // Casting between pointer and function types is allowed (because they're both
        // just functions).
        (AType::Pointer(_), target) => target.is_numeric() || target.is_fn(),
        (source, AType::Pointer(APointerType { is_mut: false, .. })) => {
            source.is_numeric() || source == &AType::Str || source.is_fn()
        }

        _ => false,
    }
}

/// Returns the type of the value that would result from performing `op` on operands with
/// `operand_type_key`. If no `operand_type_key` was specified, falls back to default result type.
fn get_result_type(
    ctx: &ProgramContext,
    op: &Operator,
    operand_type_key: Option<TypeKey>,
) -> TypeKey {
    match op {
        // Mathematical operations result in the same type as their operands.
        Operator::Add
        | Operator::Subtract
        | Operator::Multiply
        | Operator::Divide
        | Operator::Modulo => match operand_type_key {
            Some(type_key) => type_key,
            None => ctx.int_type_key(),
        },

        // Logical operators result in bools.
        Operator::LogicalAnd | Operator::LogicalOr => ctx.bool_type_key(),

        // Bitwise operators result in numerics matching their operands.
        Operator::BitwiseAnd
        | Operator::BitwiseOr
        | Operator::BitwiseXor
        | Operator::BitwiseLeftShift
        | Operator::BitwiseRightShift => match operand_type_key {
            Some(type_key) => type_key,
            None => ctx.unknown_type_key(),
        },

        // Equality operators result in bools.
        Operator::EqualTo | Operator::NotEqualTo | Operator::Like | Operator::NotLike => {
            ctx.bool_type_key()
        }

        // Comparators result in bools.
        Operator::GreaterThan
        | Operator::LessThan
        | Operator::GreaterThanOrEqual
        | Operator::LessThanOrEqual => ctx.bool_type_key(),

        Operator::As => match operand_type_key {
            Some(type_key) => type_key,
            None => ctx.unknown_type_key(),
        },

        // If this happens, the something is badly broken.
        other => panic!("unexpected operator {}", other),
    }
}

/// Computes the operand type that should be expected for operator `op` that yields a result of
/// `expected_result_type_key`. Returns `None` if it's unclear what the operand type should be.
fn get_expected_operand_type_key(
    ctx: &ProgramContext,
    op: &Operator,
    expected_result_type_key: TypeKey,
) -> Option<TypeKey> {
    match op {
        Operator::Add
        | Operator::Subtract
        | Operator::Multiply
        | Operator::Divide
        | Operator::Modulo => Some(expected_result_type_key),

        Operator::LogicalAnd | Operator::LogicalOr => Some(ctx.bool_type_key()),

        Operator::BitwiseAnd
        | Operator::BitwiseOr
        | Operator::BitwiseXor
        | Operator::BitwiseLeftShift
        | Operator::BitwiseRightShift => Some(expected_result_type_key),

        Operator::EqualTo | Operator::NotEqualTo | Operator::Like | Operator::NotLike => None,

        Operator::GreaterThan
        | Operator::LessThan
        | Operator::GreaterThanOrEqual
        | Operator::LessThanOrEqual => None,

        Operator::As => None,

        // If this happens, the something is badly broken.
        other => panic!("unexpected operator {}", other),
    }
}

fn analyze_type_cast(
    ctx: &mut ProgramContext,
    expr: Expression,
    target_type: Type,
    span: Span,
) -> AExpr {
    let left_expr = AExpr::from(ctx, expr, None, false, false);
    let target_type_key = ctx.resolve_type(&target_type);
    let left_type = ctx.must_get_type(left_expr.type_key);
    let a_target_type = ctx.must_get_type(target_type_key);

    // Skip the check if the left expression already failed analysis.
    // Also make sure the type keys are actually different. If not, this is a
    // superfluous type cast.
    if !left_type.is_unknown() && !is_valid_type_cast(left_type, a_target_type) {
        ctx.insert_err(AnalyzeError::new(
            ErrorKind::InvalidTypeCast,
            format_code!(
                "cannot cast value of type {} to type {}",
                left_type.display(ctx),
                a_target_type.display(ctx)
            )
            .as_str(),
            &left_expr,
        ));

        AExpr::new_zero_value(ctx, target_type)
    } else if left_expr.type_key == target_type_key {
        ctx.insert_err(AnalyzeError::new(
            ErrorKind::SuperfluousTypeCast,
            format_code!(
                "{} already has type {}",
                left_expr.display(ctx),
                ctx.display_type_for_key(target_type_key)
            )
            .as_str(),
            &span,
        ));

        AExpr::new_zero_value(ctx, target_type)
    } else {
        AExpr {
            kind: AExprKind::TypeCast(Box::new(left_expr), target_type_key),
            type_key: target_type_key,
            span,
        }
    }
}

fn analyze_tuple_init(
    ctx: &mut ProgramContext,
    tuple_init: TupleInit,
    maybe_expected_type_key: Option<TypeKey>,
    span: Span,
) -> AExpr {
    let maybe_expected_field_type_keys = match maybe_expected_type_key {
        Some(tk) => {
            if let AType::Tuple(tuple_type) = ctx.must_get_type(tk) {
                let mut field_type_keys = Vec::with_capacity(tuple_type.fields.len());
                for i in 0..tuple_type.fields.len() {
                    field_type_keys.insert(i, tuple_type.get_field_type_key(i).unwrap());
                }

                Some(field_type_keys)
            } else {
                None
            }
        }
        None => None,
    };

    let a_init = ATupleInit::from(ctx, &tuple_init, maybe_expected_field_type_keys);
    let type_key = a_init.type_key;
    AExpr {
        kind: AExprKind::TupleInit(a_init),
        type_key,
        span,
    }
}

fn analyze_array_init(
    ctx: &mut ProgramContext,
    array_init: ArrayInit,
    maybe_expected_type_key: Option<TypeKey>,
    span: Span,
) -> AExpr {
    let maybe_element_type_key = match maybe_expected_type_key {
        Some(tk) => {
            if let AType::Array(array_type) = ctx.must_get_type(tk) {
                array_type.maybe_element_type_key
            } else {
                None
            }
        }
        None => None,
    };

    let a_init = AArrayInit::from(ctx, &array_init, maybe_element_type_key);
    let type_key = a_init.type_key;
    AExpr {
        kind: AExprKind::ArrayInit(a_init),
        type_key,
        span,
    }
}

fn analyze_fn_call(ctx: &mut ProgramContext, fn_call: FuncCall, span: Span) -> AExpr {
    let a_call = AFnCall::from(ctx, &fn_call);
    match a_call.maybe_ret_type_key.clone() {
        Some(type_key) => AExpr {
            kind: AExprKind::FunctionCall(Box::new(a_call)),
            type_key,
            span,
        },

        _ => {
            // The function does not have a return value. Record the error and return some
            // zero-value instead.
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::ExpectedReturnValue,
                format_code!(
                    "{} has no return value, but is called in an expression",
                    a_call.display(ctx),
                )
                .as_str(),
                &fn_call,
            ));

            AExpr::new_zero_value(ctx, Type::Unresolved(UnresolvedType::unresolved_none()))
        }
    }
}

fn analyze_anon_fn(ctx: &mut ProgramContext, anon_fn: Function, span: Span) -> AExpr {
    // Give the anonymous function a unique name based on the order in which it appears
    // inside the current scope.
    let mut sig = anon_fn.signature.clone();
    sig.name = ctx.new_anon_fn_name();

    let a_closure = AClosure::from(
        ctx,
        &anon_fn.body,
        ScopeKind::FnBody(sig.name.clone()),
        sig.args.clone(),
        sig.maybe_ret_type.clone(),
    );

    // Make sure the function return conditions are satisfied by the closure.
    if sig.maybe_ret_type.is_some() {
        check_closure_returns(ctx, &a_closure, &ScopeKind::FnBody(sig.name.clone()));
    }

    let a_fn = AFn {
        signature: AFnSig::from(ctx, &sig),
        body: a_closure,
    };
    let type_key = a_fn.signature.type_key;

    AExpr {
        span,
        kind: AExprKind::AnonFunction(Box::new(a_fn)),
        type_key,
    }
}

fn analyze_unary_op(
    ctx: &mut ProgramContext,
    op: &Operator,
    expr: &Expression,
    right_expr: &Expression,
    span: Span,
) -> AExpr {
    match op {
        Operator::LogicalNot => {
            let a_expr = AExpr::from(
                ctx,
                right_expr.clone(),
                Some(ctx.bool_type_key()),
                false,
                false,
            );

            // Make sure the expression has type bool.
            if !ctx.must_get_type(a_expr.type_key).is_bool() {
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::MismatchedTypes,
                    format_code!(
                        "unary operator {} cannot be applied to value of type {}",
                        "!",
                        a_expr.display(ctx),
                    )
                    .as_str(),
                    expr,
                ));

                AExpr::new_zero_value(ctx, Type::new_unresolved("bool"))
            } else {
                AExpr {
                    type_key: a_expr.type_key,
                    kind: AExprKind::UnaryOperation(Operator::LogicalNot, Box::new(a_expr)),
                    span,
                }
            }
        }

        Operator::Reference => {
            let operand_expr = AExpr::from(ctx, right_expr.clone(), None, false, false);
            let a_ptr_type = APointerType::new(operand_expr.type_key, false);
            let type_key = ctx.insert_type(AType::Pointer(a_ptr_type));

            AExpr {
                type_key,
                kind: AExprKind::UnaryOperation(Operator::Reference, Box::new(operand_expr)),
                span,
            }
        }

        Operator::MutReference => {
            let operand_expr = AExpr::from(ctx, right_expr.clone(), None, false, false);

            // Make sure we're allowed to take a `&mut` to this operand.
            operand_expr.check_referencable_as_mut(ctx, expr);

            let a_ptr_type = APointerType::new(operand_expr.type_key, true);
            let type_key = ctx.insert_type(AType::Pointer(a_ptr_type));

            AExpr {
                type_key,
                kind: AExprKind::UnaryOperation(Operator::MutReference, Box::new(operand_expr)),
                span,
            }
        }

        Operator::Defererence => {
            let operand_expr = AExpr::from(ctx, right_expr.clone(), None, false, false);
            let operand_expr_type = ctx.must_get_type(operand_expr.type_key);

            // Make sure the operand expression is of a pointer type.
            match operand_expr_type {
                AType::Pointer(ptr_type) => AExpr {
                    type_key: ptr_type.pointee_type_key,
                    kind: AExprKind::UnaryOperation(Operator::Defererence, Box::new(operand_expr)),
                    span,
                },

                other => {
                    // Don't display a redundant error if the operand expression already
                    // failed analysis.
                    if !other.is_unknown() {
                        ctx.insert_err(AnalyzeError::new(
                            ErrorKind::MismatchedTypes,
                            format_code!("cannot dereference value of type {}", other.display(ctx))
                                .as_str(),
                            expr,
                        ));
                    }

                    AExpr::new_zero_value(ctx, Type::new_unresolved("<unknown>"))
                }
            }
        }

        Operator::Subtract => {
            let operand_expr = AExpr::from(ctx, right_expr.clone(), None, false, false);
            let operand_expr_type = ctx.must_get_type(operand_expr.type_key);

            // Make sure the operand expression is of a signed numeric type since we'll
            // have to flip its sign.
            if operand_expr_type.is_numeric() && operand_expr_type.is_signed() {
                AExpr {
                    type_key: operand_expr.type_key,
                    kind: AExprKind::UnaryOperation(Operator::Subtract, Box::new(operand_expr)),
                    span,
                }
            } else {
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::MismatchedTypes,
                    format!(
                        "cannot negate value of {} type {}",
                        match operand_expr_type.is_numeric() {
                            true => "unsigned",
                            false => "non-numeric",
                        },
                        format_code!(operand_expr_type)
                    )
                    .as_str(),
                    expr,
                ));

                AExpr::new_zero_value(ctx, Type::new_unresolved("<unknown>"))
            }
        }

        Operator::BitwiseNot => {
            let operand_expr = AExpr::from(ctx, right_expr.clone(), None, false, false);
            let operand_expr_type = ctx.must_get_type(operand_expr.type_key);

            // Make sure the operand is of an integer type.
            if operand_expr_type.is_integer() {
                AExpr {
                    type_key: operand_expr.type_key,
                    kind: AExprKind::UnaryOperation(Operator::BitwiseNot, Box::new(operand_expr)),
                    span,
                }
            } else {
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::MismatchedTypes,
                    format!(
                        "cannot bitwise negate value of non-integer type {}",
                        format_code!(operand_expr_type)
                    )
                    .as_str(),
                    expr,
                ));

                AExpr::new_zero_value(ctx, Type::new_unresolved("<unknown>"))
            }
        }

        _ => {
            panic!("unexpected unary operator {}", op)
        }
    }
}

fn analyze_binary_op(
    ctx: &mut ProgramContext,
    op: Operator,
    left_expr: Expression,
    right_expr: Expression,
    maybe_expected_type_key: Option<TypeKey>,
    span: Span,
) -> AExpr {
    let maybe_expected_operand_tk = match maybe_expected_type_key {
        Some(tk) => get_expected_operand_type_key(ctx, &op, tk),
        None => None,
    };

    let a_left = AExpr::from(ctx, left_expr, maybe_expected_operand_tk, false, false);

    // If there is no expected operand type, we should try to coerce the right
    // expression to the type of the left expression, but only if it's not a bit shift operation.
    // Bit shift operations are currently the only ones where the left and right operands can
    // have mismatched types.
    let maybe_expected_right_tk = match op.is_bitshift() {
        true => None,
        false => Some(maybe_expected_operand_tk.unwrap_or(a_left.type_key)),
    };
    let a_right = AExpr::from(ctx, right_expr, maybe_expected_right_tk, false, true);

    // If we couldn't resolve both of the operand types, we'll skip any further
    // type checks by returning early.
    let left_type = ctx.must_get_type(a_left.type_key);
    let right_type = ctx.must_get_type(a_right.type_key);
    if left_type.is_unknown() || right_type.is_unknown() {
        return AExpr {
            kind: AExprKind::BinaryOperation(
                Box::new(a_left.clone()),
                op.clone(),
                Box::new(a_right),
            ),
            type_key: get_result_type(ctx, &op, None),
            span,
        };
    }

    // Check that the operands are compatible with the operator and one another.
    let (maybe_operand_type_key, errors) = match check_operand_types(ctx, &a_left, &op, &a_right) {
        Ok(maybe_type_key) => (maybe_type_key, vec![]),
        Err(errs) => (None, errs),
    };

    // Add any errors we collected to the program context. We're doing it this way
    // instead of adding errors to the program context immediately to avoid borrowing
    // issues.
    for err in errors {
        ctx.insert_err(err);
    }

    AExpr {
        kind: AExprKind::BinaryOperation(Box::new(a_left.clone()), op.clone(), Box::new(a_right)),
        type_key: get_result_type(ctx, &op, maybe_operand_type_key),
        span,
    }
}

fn analyze_symbol(ctx: &mut ProgramContext, symbol: Symbol, allow_type: bool, span: Span) -> AExpr {
    let a_symbol = ASymbol::from(ctx, &symbol, true, allow_type, false, None);
    AExpr {
        type_key: a_symbol.type_key,
        kind: AExprKind::Symbol(a_symbol),
        span,
    }
}

fn analyze_from(
    ctx: &mut ProgramContext,
    from: &From,
    maybe_expected_type_key: Option<TypeKey>,
) -> AExpr {
    ctx.push_scope(Scope::new(
        ScopeKind::FromBody,
        vec![],
        maybe_expected_type_key,
    ));
    let statement = AStatement::from(ctx, &from.statement);

    // Determined the yielded type key based on the type key that was set on
    // the `from` block scope. This will be the expected yield type key if one
    // was specified, or it will be a value determined based on the type of
    // the first value `yielded` from the statement. It could also be `None`
    // in the case where the statement does not contain a `yield`.
    let type_key = match ctx.pop_scope().yield_type_key() {
        Some(tk) => tk,
        None => ctx.unknown_type_key(),
    };

    // Make sure all possible branches of the statement yield a value.
    let mut closure = AClosure::new(vec![statement], from.statement.span().clone());
    check_closure_yields(ctx, &closure, &ScopeKind::FromBody);

    AExpr {
        type_key,
        kind: AExprKind::From(Box::new(closure.statements.remove(0))),
        span: from.span().clone(),
    }
}

fn analyze_expr_with_pref(
    ctx: &mut ProgramContext,
    expr: Expression,
    maybe_expected_type_key: Option<TypeKey>,
    allow_type: bool,
    prefer_method: bool,
    span: Span,
) -> AExpr {
    match expr {
        Expression::TypeCast(expr, target_type) => analyze_type_cast(ctx, *expr, target_type, span),

        Expression::Symbol(symbol) => analyze_symbol(ctx, symbol, allow_type, span),

        Expression::BoolLiteral(b) => AExpr {
            kind: AExprKind::BoolLiteral(b.value),
            type_key: ctx.bool_type_key(),
            span,
        },

        Expression::I8Literal(i) => AExpr {
            kind: AExprKind::I8Literal(i.value),
            type_key: ctx.i8_type_key(),
            span,
        },

        Expression::U8Literal(i) => AExpr {
            kind: AExprKind::U8Literal(i.value),
            type_key: ctx.u8_type_key(),
            span,
        },

        Expression::I32Literal(i) => AExpr {
            kind: AExprKind::I32Literal(i.value),
            type_key: ctx.i32_type_key(),
            span,
        },

        Expression::U32Literal(i) => AExpr {
            kind: AExprKind::U32Literal(i.value),
            type_key: ctx.u32_type_key(),
            span,
        },

        Expression::F32Literal(i) => AExpr {
            kind: AExprKind::F32Literal(i.value),
            type_key: ctx.f32_type_key(),
            span,
        },

        Expression::I64Literal(i) => AExpr {
            kind: AExprKind::I64Literal(i.value),
            type_key: ctx.i64_type_key(),
            span,
        },

        Expression::U64Literal(i) => AExpr {
            kind: AExprKind::U64Literal(i.value),
            type_key: ctx.u64_type_key(),
            span,
        },

        Expression::F64Literal(i) => AExpr {
            kind: AExprKind::F64Literal(i.value, i.has_suffix),
            type_key: ctx.f64_type_key(),
            span,
        },

        Expression::IntLiteral(i) => AExpr {
            kind: AExprKind::IntLiteral(i.value, i.has_suffix),
            type_key: ctx.int_type_key(),
            span,
        },

        Expression::UintLiteral(i) => AExpr {
            kind: AExprKind::UintLiteral(i.value),
            type_key: ctx.uint_type_key(),
            span,
        },

        Expression::StrLiteral(s) => AExpr {
            kind: AExprKind::StrLiteral(s.value.clone()),
            type_key: ctx.str_type_key(),
            span,
        },

        Expression::StructInit(struct_init) => {
            let a_init = AStructInit::from(ctx, &struct_init);
            let type_key = a_init.type_key;
            AExpr {
                kind: AExprKind::StructInit(a_init),
                type_key,
                span,
            }
        }

        Expression::EnumInit(enum_init) => {
            let a_init = AEnumVariantInit::from(ctx, &enum_init);
            let type_key = a_init.type_key;
            AExpr {
                kind: AExprKind::EnumInit(a_init),
                type_key,
                span,
            }
        }

        Expression::TupleInit(tuple_init) => {
            analyze_tuple_init(ctx, tuple_init, maybe_expected_type_key, span)
        }

        Expression::ArrayInit(array_init) => {
            analyze_array_init(ctx, *array_init, maybe_expected_type_key, span)
        }

        Expression::SizeOf(sizeof) => {
            let type_key = ctx.resolve_type(&sizeof.typ);
            AExpr {
                kind: AExprKind::Sizeof(type_key),
                type_key: ctx.uint_type_key(),
                span,
            }
        }

        Expression::FunctionCall(fn_call) => {
            // Analyze the function call and ensure it has a return type.
            analyze_fn_call(ctx, *fn_call, span)
        }

        Expression::Index(index) => {
            let a_index = AIndex::from(ctx, &index);
            AExpr {
                type_key: a_index.result_type_key,
                kind: AExprKind::Index(Box::new(a_index)),
                span,
            }
        }

        Expression::MemberAccess(member_access) => {
            // Prefer methods if the expected type is a function.
            let prefer_method = prefer_method
                || match maybe_expected_type_key {
                    Some(tk) => ctx.must_get_type(tk).is_fn(),
                    None => false,
                };

            let access = AMemberAccess::from(ctx, &member_access, prefer_method);
            AExpr {
                type_key: access.member_type_key,
                kind: AExprKind::MemberAccess(Box::new(access)),
                span,
            }
        }

        Expression::AnonFunction(anon_fn) => analyze_anon_fn(ctx, *anon_fn, span),

        Expression::Lambda(_) => {
            todo!();
        }

        Expression::UnaryOperation(ref op, ref right_expr) => {
            analyze_unary_op(ctx, op, &expr, right_expr, span)
        }

        Expression::BinaryOperation(left_expr, op, right_expr) => analyze_binary_op(
            ctx,
            op,
            *left_expr,
            *right_expr,
            maybe_expected_type_key,
            span,
        ),

        Expression::From(from) => analyze_from(ctx, &from, maybe_expected_type_key),
    }
}

#[cfg(test)]
mod tests {
    use crate::analyzer::ast::arg::AArg;
    use crate::analyzer::ast::closure::AClosure;
    use crate::analyzer::ast::expr::{AExpr, AExprKind};
    use crate::analyzer::ast::fn_call::AFnCall;
    use crate::analyzer::ast::func::{AFn, AFnSig};
    use crate::analyzer::ast::r#type::AType;
    use crate::analyzer::ast::symbol::ASymbol;
    use crate::analyzer::error::{AnalyzeError, ErrorKind};
    use crate::analyzer::prog_context::ProgramContext;
    use crate::analyzer::scope::ScopedSymbol;
    use crate::parser::ast::arg::Argument;
    use crate::parser::ast::bool_lit::BoolLit;
    use crate::parser::ast::expr::Expression;
    use crate::parser::ast::func_call::FuncCall;
    use crate::parser::ast::func_sig::FunctionSignature;
    use crate::parser::ast::i64_lit::I64Lit;
    use crate::parser::ast::op::Operator;
    use crate::parser::ast::r#type::Type;
    use crate::parser::ast::str_lit::StrLit;
    use crate::parser::ast::symbol::Symbol;

    #[test]
    fn analyze_i64_literal() {
        let mut ctx = ProgramContext::new_with_host_ptr_width("test", vec!["test"]);
        let expr = Expression::I64Literal(I64Lit::new_with_default_pos(1));
        let result = AExpr::from(&mut ctx, expr, None, false, false);
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::I64Literal(1),
                type_key: ctx.i64_type_key(),
                span: Default::default(),
            }
        );
    }

    #[test]
    fn analyze_bool_literal() {
        let mut ctx = ProgramContext::new_with_host_ptr_width("test", vec!["test"]);
        let expr = Expression::BoolLiteral(BoolLit::new_with_default_pos(false));
        let result = AExpr::from(&mut ctx, expr, None, false, false);
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::BoolLiteral(false),
                type_key: ctx.bool_type_key(),
                span: Default::default(),
            },
        );
    }

    #[test]
    fn analyze_string_literal() {
        let mut ctx = ProgramContext::new_with_host_ptr_width("test", vec!["test"]);
        let expr = Expression::StrLiteral(StrLit::new_with_default_pos("test"));
        let result = AExpr::from(&mut ctx, expr, None, false, false);
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::StrLiteral(String::from("test")),
                type_key: ctx.str_type_key(),
                span: Default::default(),
            }
        );
    }

    #[test]
    fn analyze_var() {
        let mut ctx = ProgramContext::new_with_host_ptr_width("test", vec!["test"]);
        ctx.insert_symbol(ScopedSymbol::new("myvar", ctx.str_type_key(), false));
        let result = AExpr::from(
            &mut ctx,
            Expression::Symbol(Symbol::new_with_default_pos("myvar")),
            None,
            false,
            false,
        );
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::Symbol(
                    ASymbol::new_with_default_pos("myvar", ctx.str_type_key(),)
                ),
                type_key: ctx.str_type_key(),
                span: Default::default(),
            }
        );
    }

    #[test]
    fn analyze_invalid_var() {
        let mut ctx = ProgramContext::new_with_host_ptr_width("test", vec!["test"]);
        let result = AExpr::from(
            &mut ctx,
            Expression::Symbol(Symbol::new_with_default_pos("myvar")),
            None,
            false,
            false,
        );
        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::Symbol(ASymbol::new_with_default_pos(
                    "myvar",
                    ctx.unknown_type_key(),
                )),
                type_key: ctx.unknown_type_key(),
                span: Default::default(),
            }
        );
        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::UndefSymbol,
                ..
            }
        ));
    }

    #[test]
    fn analyze_fn_call() {
        let mut ctx = ProgramContext::new_with_host_ptr_width("test", vec!["test"]);
        let fn_sig = FunctionSignature::new_with_default_pos(
            "do_thing",
            vec![Argument::new_with_default_pos(
                "first",
                Type::new_unresolved("bool"),
                false,
            )],
            Some(Type::new_unresolved("str")),
        );
        let fn_type_key = ctx.resolve_type(&Type::Function(Box::new(fn_sig.clone())));
        let a_fn = AFn {
            signature: AFnSig {
                name: "do_thing".to_string(),
                mangled_name: "test::do_thing".to_string(),
                args: vec![AArg {
                    name: "first".to_string(),
                    type_key: ctx.bool_type_key(),
                    is_mut: false,
                }],
                maybe_ret_type_key: Some(ctx.str_type_key()),
                type_key: fn_type_key,
                maybe_impl_type_key: None,
                params: None,
            },
            body: AClosure::new_empty(),
        };

        // Add the function and its type to the context so they can be retrieved when analyzing
        // the expression that calls the function.
        ctx.insert_fn(a_fn.clone());
        ctx.insert_type(AType::from_fn_sig(a_fn.signature.clone()));

        // Analyze the function call expression.
        let fn_call = FuncCall::new_with_default_pos(
            Expression::Symbol(Symbol::new_with_default_pos("do_thing")),
            vec![Expression::BoolLiteral(BoolLit::new_with_default_pos(true))],
        );
        let call_expr = Expression::FunctionCall(Box::new(fn_call.clone()));
        let result = AExpr::from(&mut ctx, call_expr, None, false, false);

        // Check that analysis succeeded.
        assert!(ctx.errors().is_empty());
        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::FunctionCall(Box::new(AFnCall {
                    fn_expr: AExpr::new_with_default_pos(
                        AExprKind::Symbol(ASymbol::new_with_default_pos(
                            "test::do_thing",
                            a_fn.signature.type_key,
                        )),
                        a_fn.signature.type_key,
                    ),
                    args: vec![AExpr {
                        kind: AExprKind::BoolLiteral(true),
                        type_key: ctx.bool_type_key(),
                        span: Default::default(),
                    }],
                    maybe_ret_type_key: Some(ctx.str_type_key()),
                })),
                type_key: ctx.str_type_key(),
                span: Default::default(),
            },
        );
    }

    #[test]
    fn fn_call_no_return() {
        let mut ctx = ProgramContext::new_with_host_ptr_width("test", vec!["test"]);
        let fn_sig = FunctionSignature::new_with_default_pos("do_thing", vec![], None);
        let fn_type_key = ctx.resolve_type(&Type::Function(Box::new(fn_sig.clone())));
        let a_fn = AFn {
            signature: AFnSig {
                name: "do_thing".to_string(),
                mangled_name: "test::do_thing".to_string(),
                args: vec![],
                maybe_ret_type_key: None,
                type_key: fn_type_key,
                maybe_impl_type_key: None,
                params: None,
            },
            body: AClosure::new_empty(),
        };

        // Add the function and its type to the context, so they can be retrieved when analyzing
        // the expression that calls the function.
        ctx.insert_fn(a_fn.clone());
        ctx.insert_type(AType::from_fn_sig(a_fn.signature.clone()));

        // Analyze the function call expression.
        let result = AExpr::from(
            &mut ctx,
            Expression::BinaryOperation(
                Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(1))),
                Operator::Add,
                Box::new(Expression::FunctionCall(Box::new(
                    FuncCall::new_with_default_pos(
                        Expression::Symbol(Symbol::new_with_default_pos("do_thing")),
                        vec![],
                    ),
                ))),
            ),
            None,
            false,
            false,
        );

        match result {
            AExpr {
                kind: AExprKind::BinaryOperation(left, Operator::Add, right),
                type_key,
                ..
            } => {
                assert_eq!(
                    *left,
                    AExpr {
                        kind: AExprKind::I64Literal(1),
                        type_key: ctx.i64_type_key(),
                        span: Default::default(),
                    }
                );
                assert_eq!(
                    *right,
                    AExpr {
                        kind: AExprKind::Unknown,
                        type_key: ctx.none_type_key(),
                        span: Default::default(),
                    }
                );
                assert_eq!(type_key, ctx.int_type_key())
            }
            other => panic!("incorrect result {}", other),
        }

        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::ExpectedReturnValue,
                ..
            }
        ));
    }

    #[test]
    fn fn_call_missing_arg() {
        let mut ctx = ProgramContext::new_with_host_ptr_width("test", vec!["test"]);
        let fn_sig = FunctionSignature::new_with_default_pos(
            "do_thing",
            vec![
                Argument::new_with_default_pos("arg1", Type::new_unresolved("bool"), false),
                Argument::new_with_default_pos("arg2", Type::new_unresolved("i64"), false),
            ],
            Some(Type::new_unresolved("bool")),
        );
        let fn_type_key = ctx.resolve_type(&Type::Function(Box::new(fn_sig)));
        let a_fn = AFn {
            signature: AFnSig {
                name: "do_thing".to_string(),
                mangled_name: "test::do_thing".to_string(),
                args: vec![
                    AArg {
                        name: "arg1".to_string(),
                        type_key: ctx.bool_type_key(),
                        is_mut: false,
                    },
                    AArg {
                        name: "arg2".to_string(),
                        type_key: ctx.i64_type_key(),
                        is_mut: false,
                    },
                ],
                maybe_ret_type_key: Some(ctx.bool_type_key()),
                type_key: fn_type_key,
                maybe_impl_type_key: None,
                params: None,
            },
            body: AClosure::new_empty(),
        };

        // Add the function and its type to the context, so they can be retrieved when analyzing
        // the expression that calls the function.
        ctx.insert_fn(a_fn.clone());
        ctx.insert_type(AType::from_fn_sig(a_fn.signature.clone()));

        // Analyze the function call expression.
        let result = AExpr::from(
            &mut ctx,
            Expression::FunctionCall(Box::new(FuncCall::new_with_default_pos(
                Expression::Symbol(Symbol::new_with_default_pos("do_thing")),
                vec![Expression::BoolLiteral(BoolLit::new_with_default_pos(true))],
            ))),
            None,
            false,
            false,
        );

        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::FunctionCall(Box::new(AFnCall {
                    fn_expr: AExpr::new_with_default_pos(
                        AExprKind::Symbol(ASymbol::new_with_default_pos(
                            "test::do_thing",
                            a_fn.signature.type_key,
                        )),
                        fn_type_key
                    ),
                    args: vec![],
                    maybe_ret_type_key: Some(ctx.unknown_type_key()),
                })),
                type_key: ctx.unknown_type_key(),
                span: Default::default(),
            }
        );

        match result.kind {
            AExprKind::FunctionCall(call) => {
                assert_eq!(
                    call.fn_expr,
                    AExpr::new_with_default_pos(
                        AExprKind::Symbol(ASymbol::new_with_default_pos(
                            "test::do_thing",
                            a_fn.signature.type_key,
                        )),
                        a_fn.signature.type_key,
                    )
                );

                assert_eq!(call.maybe_ret_type_key, Some(ctx.unknown_type_key()));
                assert_eq!(call.args.len(), 0);
            }
            _ => unreachable!(),
        };

        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::WrongNumberOfArgs,
                ..
            }
        ));
    }

    #[test]
    fn fn_call_invalid_arg_type() {
        let mut ctx = ProgramContext::new_with_host_ptr_width("test", vec!["test"]);
        let fn_sig = FunctionSignature::new_with_default_pos(
            "do_thing",
            vec![Argument::new_with_default_pos(
                "arg",
                Type::new_unresolved("bool"),
                false,
            )],
            Some(Type::new_unresolved("bool")),
        );
        let a_fn = AFn {
            signature: AFnSig {
                name: "do_thing".to_string(),
                mangled_name: "test::do_thing".to_string(),
                args: vec![AArg {
                    name: "arg".to_string(),
                    type_key: ctx.bool_type_key(),
                    is_mut: false,
                }],
                maybe_ret_type_key: Some(ctx.bool_type_key()),
                type_key: ctx.resolve_type(&Type::Function(Box::new(fn_sig))),
                maybe_impl_type_key: None,
                params: None,
            },
            body: AClosure::new_empty(),
        };

        // Add the function and its type to the context so they can be retrieved when analyzing
        // the expression that calls the function.
        ctx.insert_fn(a_fn.clone());
        ctx.insert_type(AType::from_fn_sig(a_fn.signature.clone()));

        // Analyze the function call expression.
        let result = AExpr::from(
            &mut ctx,
            Expression::FunctionCall(Box::new(FuncCall::new_with_default_pos(
                Expression::Symbol(Symbol::new_with_default_pos("do_thing")),
                vec![Expression::I64Literal(I64Lit::new_with_default_pos(1))],
            ))),
            None,
            false,
            false,
        );

        assert_eq!(
            result,
            AExpr::new_with_default_pos(
                AExprKind::FunctionCall(Box::new(AFnCall {
                    fn_expr: AExpr::new_with_default_pos(
                        AExprKind::Symbol(ASymbol::new_with_default_pos(
                            "test::do_thing",
                            a_fn.signature.type_key,
                        )),
                        a_fn.signature.type_key,
                    ),
                    args: vec![AExpr {
                        kind: AExprKind::I64Literal(1),
                        type_key: ctx.i64_type_key(),
                        span: Default::default(),
                    }],
                    maybe_ret_type_key: Some(ctx.bool_type_key()),
                })),
                ctx.bool_type_key(),
            )
        );

        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            }
        ));
    }

    #[test]
    fn binary_op_invalid_operand_types() {
        let mut ctx = ProgramContext::new_with_host_ptr_width("test", vec!["test"]);
        let result = AExpr::from(
            &mut ctx,
            Expression::BinaryOperation(
                Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(1))),
                Operator::Add,
                Box::new(Expression::StrLiteral(StrLit::new_with_default_pos("asdf"))),
            ),
            None,
            false,
            false,
        );

        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::BinaryOperation(
                    Box::new(AExpr {
                        kind: AExprKind::I64Literal(1),
                        type_key: ctx.i64_type_key(),
                        span: Default::default(),
                    }),
                    Operator::Add,
                    Box::new(AExpr {
                        kind: AExprKind::StrLiteral("asdf".to_string()),
                        type_key: ctx.str_type_key(),
                        span: Default::default(),
                    })
                ),
                type_key: ctx.int_type_key(),
                span: Default::default(),
            }
        );

        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            }
        ));

        let mut ctx = ProgramContext::new_with_host_ptr_width("test", vec!["test"]);
        let result = AExpr::from(
            &mut ctx,
            Expression::BinaryOperation(
                Box::new(Expression::StrLiteral(StrLit::new_with_default_pos("asdf"))),
                Operator::Add,
                Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(1))),
            ),
            None,
            false,
            false,
        );

        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::BinaryOperation(
                    Box::new(AExpr {
                        kind: AExprKind::StrLiteral("asdf".to_string()),
                        type_key: ctx.str_type_key(),
                        span: Default::default(),
                    }),
                    Operator::Add,
                    Box::new(AExpr {
                        kind: AExprKind::I64Literal(1),
                        type_key: ctx.i64_type_key(),
                        span: Default::default(),
                    })
                ),
                type_key: ctx.int_type_key(),
                span: Default::default(),
            }
        );

        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            }
        ));
    }

    #[test]
    fn unary_op() {
        let mut ctx = ProgramContext::new_with_host_ptr_width("test", vec!["test"]);
        let result = AExpr::from(
            &mut ctx,
            Expression::UnaryOperation(
                Operator::LogicalNot,
                Box::new(Expression::I64Literal(I64Lit::new_with_default_pos(1))),
            ),
            None,
            false,
            false,
        );

        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::BoolLiteral(false),
                type_key: ctx.bool_type_key(),
                span: Default::default(),
            }
        );

        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            }
        ));
    }

    #[test]
    fn unary_op_invalid_operand_type() {
        let mut ctx = ProgramContext::new_with_host_ptr_width("test", vec!["test"]);
        let result = AExpr::from(
            &mut ctx,
            Expression::UnaryOperation(
                Operator::LogicalNot,
                Box::new(Expression::StrLiteral(StrLit::new_with_default_pos("s"))),
            ),
            None,
            false,
            false,
        );

        assert_eq!(
            result,
            AExpr {
                kind: AExprKind::BoolLiteral(false),
                type_key: ctx.bool_type_key(),
                span: Default::default(),
            }
        );

        assert!(matches!(
            ctx.errors()
                .values()
                .collect::<Vec<&AnalyzeError>>()
                .get(0)
                .unwrap(),
            AnalyzeError {
                kind: ErrorKind::MismatchedTypes,
                ..
            }
        ));
    }
}
