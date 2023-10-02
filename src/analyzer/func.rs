use std::collections::VecDeque;
use std::fmt;
use std::fmt::Formatter;

use colored::Colorize;
use pluralizer::pluralize;

use crate::analyzer::closure::{check_closure_returns, RichClosure};
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::prog_context::{ProgramContext, ScopeKind};
use crate::analyzer::r#type::{RichType, TypeId};
use crate::analyzer::var::RichVar;
use crate::lexer::pos::{Locatable, Position};
use crate::parser::arg::Argument;
use crate::parser::func::Function;
use crate::parser::func_call::FunctionCall;
use crate::parser::func_sig::FunctionSignature;
use crate::parser::r#type::Type;
use crate::parser::ret::Ret;
use crate::{format_code, util};

/// Performs semantic analysis on the function signature, ensuring it doesn't match any other
/// function signature in the ProgramContext.
pub fn analyze_fn_sig(ctx: &mut ProgramContext, sig: &FunctionSignature) -> RichFnSig {
    // Add the function to the program context with an empty body, making sure it doesn't already
    // exist. We'll replace the function body when we analyze it later.
    let rich_fn_sig = RichFnSig::from(ctx, &sig);
    if ctx.add_extern_fn(rich_fn_sig.clone()).is_some() {
        ctx.add_err(AnalyzeError::new(
            ErrorKind::FunctionAlreadyDefined,
            format_code!("function {} was already defined in this scope", sig.name).as_str(),
            sig,
        ));
    }

    rich_fn_sig
}

/// Represents a semantically valid function argument.
#[derive(PartialEq, Debug, Clone)]
pub struct RichArg {
    pub name: String,
    pub type_id: TypeId,
    pub is_mut: bool,
}

impl fmt::Display for RichArg {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if self.name.is_empty() {
            write!(f, "{}", self.type_id)
        } else {
            write!(f, "{}: {}", self.name, self.type_id)
        }
    }
}

impl RichArg {
    /// Performs semantic analysis on the argument and returns an analyzed version of it.
    pub fn from(ctx: &mut ProgramContext, arg: &Argument) -> Self {
        RichArg {
            name: arg.name.to_string(),
            type_id: RichType::analyze(ctx, &arg.typ),
            is_mut: arg.is_mut,
        }
    }
}

/// Represents a semantically valid function signature.
#[derive(Debug, Clone)]
pub struct RichFnSig {
    pub name: String,
    pub args: Vec<RichArg>,
    pub ret_type_id: Option<TypeId>,
    /// Represents this function signature as a type.
    pub type_id: TypeId,
    /// The type ID of the parent type of this is a member function.
    pub impl_type_id: Option<TypeId>,
}

impl PartialEq for RichFnSig {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && util::vecs_eq(&self.args, &other.args)
            && util::optionals_are_equal(&self.ret_type_id, &other.ret_type_id)
    }
}

impl fmt::Display for RichFnSig {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "fn {}(", self.name)?;

        for (i, arg) in self.args.iter().enumerate() {
            write!(f, "{}", arg)?;

            if i != self.args.len() - 1 {
                write!(f, ", ")?;
            }
        }

        if let Some(typ) = &self.ret_type_id {
            write!(f, ") ~ {}", typ)
        } else {
            write!(f, ")")
        }
    }
}

impl RichFnSig {
    /// Analyzes a function signature and returns a semantically valid, type-rich function
    /// signature.
    pub fn from(ctx: &mut ProgramContext, sig: &FunctionSignature) -> Self {
        // Analyze the arguments.
        let mut args = vec![];
        for arg in &sig.args {
            let rich_arg = RichArg::from(ctx, &arg);
            args.push(rich_arg);
        }

        // Analyze the return type.
        let return_type = match &sig.return_type {
            Some(typ) => Some(RichType::analyze(ctx, typ)),
            None => None,
        };

        // Check if this function signature is for a member function on a type by getting the
        // impl type ID.
        let impl_type_id = match ctx.get_impl_type_id() {
            Some(type_id) => Some(type_id.clone()),
            None => None,
        };

        let rich_fn_sig = RichFnSig {
            name: sig.name.to_string(),
            args,
            ret_type_id: return_type,
            type_id: TypeId::from(Type::Function(Box::new(sig.clone()))),
            impl_type_id,
        };

        // Add the function as a resolved type to the program context. This is done because
        // functions can be used as variables and therefore need types.
        ctx.add_resolved_type(
            TypeId::from(Type::Function(Box::new(sig.clone()))),
            RichType::from_fn_sig(rich_fn_sig.clone()),
        );

        rich_fn_sig
    }

    /// Returns the fully qualified name of this function. If it's a regular function, this will
    /// just be the function name. If it's a member function, it will be `<type>::<fn_name>`.
    pub fn full_name(&self) -> String {
        match &self.impl_type_id {
            Some(type_id) => format!("{}#{}", type_id.to_string(), self.name),
            None => self.name.to_string(),
        }
    }

    /// Returns true if the function signature has `this` as its first argument.
    pub fn takes_this(&self) -> bool {
        match self.args.first() {
            Some(arg) => arg.name == "this",
            None => false,
        }
    }
}

/// Represents a semantically valid and type-rich function.
#[derive(PartialEq, Debug, Clone)]
pub struct RichFn {
    pub signature: RichFnSig,
    pub body: RichClosure,
}

impl fmt::Display for RichFn {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {{...}}", &self.signature)
    }
}

impl RichFn {
    /// Performs semantic analysis on the given function and returns a type-rich version of it.
    pub fn from(ctx: &mut ProgramContext, func: Function) -> Self {
        // Make sure we are not already inside a function. For now, functions cannot be defined
        // within other functions.
        if ctx.is_in_fn() {
            ctx.add_err(AnalyzeError::new(
                ErrorKind::InvalidStatement,
                "cannot declare functions inside other functions",
                &func,
            ));
        }

        // Analyze the function body.
        let rich_closure = RichClosure::from(
            ctx,
            func.body.clone(),
            ScopeKind::FnBody,
            func.signature.args.clone(),
            func.signature.return_type.clone(),
        );

        // Make sure the function return conditions are satisfied by the closure.
        if let Some(ret_type) = &func.signature.return_type {
            let rich_ret_type = RichType::analyze(ctx, &ret_type);
            check_closure_returns(ctx, &rich_closure, &rich_ret_type, &ScopeKind::FnBody);
        }

        RichFn {
            signature: RichFnSig::from(ctx, &func.signature),
            body: rich_closure,
        }
    }
}

/// Represents a fully type-resolved and analyzed function call.
#[derive(Clone, Debug)]
pub struct RichFnCall {
    pub fn_var: RichVar,
    pub args: Vec<RichExpr>,
    pub ret_type_id: Option<TypeId>,
}

impl fmt::Display for RichFnCall {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}(", self.fn_var)?;

        for (i, arg) in self.args.iter().enumerate() {
            write!(f, "{}", arg)?;

            if i < self.args.len() - 1 {
                write!(f, ", ")?;
            }
        }

        write!(f, ")")
    }
}

impl PartialEq for RichFnCall {
    fn eq(&self, other: &Self) -> bool {
        self.fn_var == other.fn_var
            && util::vecs_eq(&self.args, &other.args)
            && util::optionals_are_equal(&self.ret_type_id, &other.ret_type_id)
    }
}

impl RichFnCall {
    /// Analyzes the given function call and returns a type-rich version of it.
    pub fn from(ctx: &mut ProgramContext, call: FunctionCall) -> Self {
        let mut errors = vec![];

        // Calls to "main" should not be allowed.
        if call.has_fn_name("main") {
            errors.push(AnalyzeError::new(
                ErrorKind::CallToMain,
                "cannot call entrypoint main",
                &call,
            ));
        }

        // Extract type information from args.
        let mut passed_args: VecDeque<RichExpr> = call
            .args
            .iter()
            .map(|arg| RichExpr::from(ctx, arg.clone()))
            .collect();

        // Get the type ID of the first argument so we can pass it as a hint to the variable
        // resolver. The variable resolver can use it as a means of locating member functions
        // for types. This is necessary for chained method calls.
        let maybe_impl_type_id = match passed_args.front() {
            Some(arg) => Some(&arg.type_id),
            None => None,
        };

        // Make sure the function exists, either as a fully analyzed function, an external function
        // signature, or a variable.
        let rich_fn_var = RichVar::from(ctx, &call.fn_var, true, maybe_impl_type_id);
        let var_type = ctx.get_resolved_type(rich_fn_var.get_type_id()).unwrap();
        let fn_sig = match var_type {
            RichType::Function(fn_sig) => fn_sig,
            other => {
                // The value being used here is not a function.
                errors.push(AnalyzeError::new(
                    ErrorKind::MismatchedTypes,
                    format_code!("type {} is not callable", other).as_str(),
                    &call,
                ));

                return RichFnCall {
                    fn_var: rich_fn_var,
                    args: vec![],
                    ret_type_id: Some(TypeId::unknown()),
                };
            }
        };

        // Clone here to avoid borrow issues.
        let ret_type = fn_sig.ret_type_id.clone();

        // If this function takes the special argument `this` and was not called directly via its
        // fully-qualified name, add the special `this` argument.
        let maybe_this = rich_fn_var.clone().without_last_member();
        let called_on_this = fn_sig.impl_type_id.is_some()
            && maybe_this.get_type_id() == fn_sig.impl_type_id.as_ref().unwrap();
        if fn_sig.takes_this() && called_on_this {
            passed_args.push_front(RichExpr::from_var(maybe_this));
        } else if !fn_sig.takes_this() && called_on_this {
            errors.push(
                AnalyzeError::new(
                    ErrorKind::MemberNotDefined,
                    format_code!(
                        "cannot call function {} on value of type {}",
                        fn_sig.name,
                        maybe_this.get_type_id(),
                    )
                    .as_str(),
                    &call,
                )
                .with_detail(
                    format_code!(
                        "Member function {} on type {} does not take {} as its first argument.",
                        fn_sig,
                        fn_sig.impl_type_id.as_ref().unwrap(),
                        "this",
                    )
                    .as_str(),
                )
                .with_help(format_code!("Did you mean to call {}?", fn_sig.full_name()).as_str()),
            );
        }

        // Make sure the right number of arguments were passed.
        if passed_args.len() != fn_sig.args.len() {
            errors.push(AnalyzeError::new(
                ErrorKind::WrongNumberOfArgs,
                format!(
                    "{} expects {}, but {} provided",
                    format_code!(fn_sig),
                    pluralize("argument", fn_sig.args.len() as isize, true),
                    pluralize("was", passed_args.len() as isize, true)
                )
                .as_str(),
                &call,
            ));
        }

        // Make sure the arguments are of the right types.
        for (passed_type_id, defined) in
            passed_args.iter().map(|arg| &arg.type_id).zip(&fn_sig.args)
        {
            // Skip the check if the argument type is unknown. This will happen if the argument
            // already failed semantic analysis.
            if ctx.get_resolved_type(passed_type_id).unwrap().is_unknown() {
                continue;
            }

            if passed_type_id != &defined.type_id {
                errors.push(AnalyzeError::new(
                    ErrorKind::MismatchedTypes,
                    format_code!(
                        "cannot use value of type {} as argument {} to {}",
                        &passed_type_id,
                        &defined,
                        &fn_sig,
                    )
                    .as_str(),
                    &call,
                ));
            }
        }

        // Now that we've finished our analysis, add all the errors to the program context. We're
        // doing it this way instead of adding errors immediately to avoid borrow issues.
        for err in errors {
            ctx.add_err(err);
        }

        RichFnCall {
            fn_var: rich_fn_var,
            args: passed_args.into(),
            ret_type_id: ret_type,
        }
    }
}

/// Represents an analyzed return statement.
#[derive(Clone, Debug)]
pub struct RichRet {
    pub val: Option<RichExpr>,
    start_pos: Position,
    end_pos: Position,
}

impl fmt::Display for RichRet {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if let Some(expr) = &self.val {
            write!(f, "return {}", expr)
        } else {
            write!(f, "return")
        }
    }
}

impl PartialEq for RichRet {
    fn eq(&self, other: &Self) -> bool {
        util::optionals_are_equal(&self.val, &other.val)
    }
}

impl Locatable for RichRet {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl RichRet {
    pub fn from(ctx: &mut ProgramContext, ret: Ret) -> Self {
        let start_pos = ret.start_pos().clone();
        let end_pos = ret.start_pos().clone();

        // Make sure we are inside a function body. If not, record the error and return a dummy
        // value.
        if !ctx.is_in_fn() {
            ctx.add_err(AnalyzeError::new(
                ErrorKind::UnexpectedReturn,
                "cannot return from outside function body",
                &ret,
            ));

            return RichRet {
                val: None,
                start_pos,
                end_pos,
            };
        }

        match ret.value {
            Some(expr) => {
                // We're returning a value. Make sure the value is of the expected type.
                let rich_expr = RichExpr::from(ctx, expr.clone());
                match ctx.return_type() {
                    Some(expected_type_id) => {
                        // Skip the type check if either type is unknown. This will be the case if
                        // semantic analysis on either type already failed.
                        let expected_type = ctx.get_resolved_type(expected_type_id).unwrap();
                        let expr_type = ctx.get_resolved_type(&rich_expr.type_id).unwrap();
                        if !expected_type.is_unknown()
                            && !expr_type.is_unknown()
                            && expected_type != expr_type
                        {
                            ctx.add_err(AnalyzeError::new(
                                ErrorKind::MismatchedTypes,
                                format_code!(
                                    "cannot return value of type {} from function with return \
                                    type {}",
                                    expr_type,
                                    expected_type,
                                )
                                .as_str(),
                                &expr,
                            ));
                        }
                    }
                    None => {
                        ctx.add_err(AnalyzeError::new(
                            ErrorKind::MismatchedTypes,
                            "cannot return value from function with no return type",
                            &expr,
                        ));
                    }
                };

                RichRet {
                    val: Some(rich_expr),
                    start_pos,
                    end_pos,
                }
            }
            None => {
                // This is an empty return. Make sure we're not expecting a return type.
                match ctx.return_type() {
                    Some(expected) => {
                        ctx.add_err(AnalyzeError::new(
                            ErrorKind::MismatchedTypes,
                            format_code!(
                                "expected return value of type {}, but found empty return",
                                expected,
                            )
                            .as_str(),
                            &ret,
                        ));
                    }
                    None => {}
                };

                RichRet {
                    val: None,
                    start_pos,
                    end_pos,
                }
            }
        }
    }
}
