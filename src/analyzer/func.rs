use std::fmt;
use std::fmt::Formatter;

use colored::Colorize;

use crate::analyzer::closure::{check_closure_returns, RichClosure};
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::prog_context::{ProgramContext, ScopeKind};
use crate::analyzer::r#type::RichType;
use crate::lexer::pos::{Locatable, Position};
use crate::parser::arg::Argument;
use crate::parser::func::Function;
use crate::parser::func_call::FunctionCall;
use crate::parser::func_sig::FunctionSignature;
use crate::parser::ret::Ret;
use crate::{format_code, util};

/// Performs semantic analysis on the function signature, ensuring it doesn't match any other
/// function signature in the ProgramContext.
pub fn analyze_fn_sig(ctx: &mut ProgramContext, sig: &FunctionSignature) -> RichFnSig {
    // Add the function to the program context with an empty body, making sure it doesn't already
    // exist. We'll replace the function body when we analyze it later.
    let rich_fn_sig = RichFnSig::from(ctx, &sig);
    if ctx.add_extern_fn(rich_fn_sig.clone()).is_some() {
        ctx.add_err(AnalyzeError::new_with_locatable(
            ErrorKind::FunctionAlreadyDefined,
            format_code!("function {} was already defined in this scope", sig.name).as_str(),
            Box::new(sig.clone()),
        ));
    }

    rich_fn_sig
}

/// Represents a semantically valid function argument.
#[derive(PartialEq, Debug, Clone)]
pub struct RichArg {
    pub name: String,
    pub typ: RichType,
}

impl fmt::Display for RichArg {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if self.name.is_empty() {
            write!(f, "{}", self.typ)
        } else {
            write!(f, "{} {}", self.typ, self.name)
        }
    }
}

impl RichArg {
    /// Performs semantic analysis on the argument and returns an analyzed version of it.
    pub fn from(ctx: &mut ProgramContext, arg: &Argument) -> Self {
        RichArg {
            name: arg.name.to_string(),
            typ: RichType::from(ctx, &arg.typ),
        }
    }
}

/// Represents a semantically valid function signature.
#[derive(Debug, Clone)]
pub struct RichFnSig {
    pub name: String,
    pub args: Vec<RichArg>,
    pub return_type: Option<RichType>,
}

impl PartialEq for RichFnSig {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && util::vectors_are_equal(&self.args, &other.args)
            && util::optionals_are_equal(&self.return_type, &other.return_type)
    }
}

impl fmt::Display for RichFnSig {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "fn {}(", self.name)?;

        for arg in self.args.iter() {
            write!(f, "{}", arg)?;

            if arg != self.args.last().unwrap() {
                write!(f, ", ")?;
            }
        }

        if let Some(typ) = &self.return_type {
            write!(f, "): {}", typ)
        } else {
            write!(f, ")")
        }
    }
}

impl RichFnSig {
    /// Analyzes a function signature and returns a semantically valid, type-rich function
    /// signature.
    pub fn from(ctx: &mut ProgramContext, sig: &FunctionSignature) -> Self {
        let mut args = vec![];
        for arg in &sig.args {
            let rich_arg = RichArg::from(ctx, &arg);
            args.push(rich_arg);
        }

        let return_type = match &sig.return_type {
            Some(typ) => Some(RichType::from(ctx, typ)),
            None => None,
        };

        RichFnSig {
            name: sig.name.to_string(),
            args,
            return_type,
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
    /// Performs semantic analysis on the given function and returns a type-rich version of it,
    /// or an error if the function is semantically invalid.
    pub fn from(ctx: &mut ProgramContext, func: Function) -> Self {
        // Make sure the function is not already defined.
        if let Some(_) = ctx.get_fn(func.signature.name.as_str()) {
            ctx.add_err(AnalyzeError::new_with_locatable(
                ErrorKind::FunctionAlreadyDefined,
                format_code!(
                    "function {} was already defined in this scope",
                    func.signature.name,
                )
                .as_str(),
                Box::new(func.clone()),
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
            let rich_ret_type = RichType::from(ctx, &ret_type);
            check_closure_returns(ctx, &rich_closure, &rich_ret_type, &ScopeKind::FnBody);
        }

        // Add the function to the program context so we can reference it later.
        let rich_fn = RichFn {
            signature: RichFnSig::from(ctx, &func.signature),
            body: rich_closure,
        };
        ctx.add_fn(rich_fn.clone());
        rich_fn
    }
}

/// Represents a fully type-resolved and analyzed function call.
#[derive(Clone, Debug)]
pub struct RichFnCall {
    pub fn_name: String,
    pub args: Vec<RichExpr>,
    pub ret_type: Option<RichType>,
}

impl fmt::Display for RichFnCall {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}(", self.fn_name)?;

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
        self.fn_name == other.fn_name
            && util::vectors_are_equal(&self.args, &other.args)
            && util::optionals_are_equal(&self.ret_type, &other.ret_type)
    }
}

impl RichFnCall {
    pub fn from(ctx: &mut ProgramContext, call: FunctionCall) -> Self {
        // Calls to "main" should not be allowed.
        if call.fn_name == "main" {
            ctx.add_err(AnalyzeError::new_with_locatable(
                ErrorKind::CallToMain,
                "cannot call entrypoint main",
                Box::new(call.clone()),
            ));
        }

        // Extract type information from args.
        let mut rich_args = vec![];
        for arg in &call.args {
            let rich_arg = RichExpr::from(ctx, arg.clone());
            rich_args.push(rich_arg);
        }

        // Make sure the function exists, either as a fully analyzed function, an external function
        // signature, or a variable.
        let fn_sig = match ctx.get_extern_fn(call.fn_name.as_str()) {
            Some(sig) => sig,
            None => match ctx.get_fn(call.fn_name.as_str()) {
                Some(decl) => &decl.signature,
                None => match ctx.get_var(call.fn_name.as_str()) {
                    Some(&RichType::Function(ref func)) => func,
                    _ => {
                        // The function is not defined, so add an error and return a zero value.
                        ctx.add_err(AnalyzeError::new_with_locatable(
                            ErrorKind::FunctionNotDefined,
                            format_code!("function {} does not exist", call.fn_name).as_str(),
                            Box::new(call.clone()),
                        ));

                        return RichFnCall {
                            fn_name: call.fn_name.clone(),
                            args: vec![],
                            ret_type: Some(RichType::Unknown("<unknown>".to_string())),
                        };
                    }
                },
            },
        };

        let ret_type = fn_sig.return_type.clone();
        let fn_name = fn_sig.name.clone();
        let fn_args = fn_sig.args.clone();

        // Make sure the right number of arguments were passed.
        if rich_args.len() != fn_sig.args.len() {
            ctx.add_err(AnalyzeError::new_with_locatable(
                ErrorKind::WrongNumberOfArgs,
                format!(
                    "function {} takes {} arguments, but {} were provided",
                    format_code!(fn_sig.name),
                    fn_sig.args.len(),
                    rich_args.len()
                )
                .as_str(),
                Box::new(call.clone()),
            ));
        }

        // Make sure the arguments are of the right types.
        for (i, (passed_type, defined)) in
            rich_args.iter().map(|a| &a.typ).zip(&fn_args).enumerate()
        {
            if !passed_type.is_compatible_with(&defined.typ) {
                let original_arg = call.args.get(i).unwrap();
                ctx.add_err(AnalyzeError::new_with_locatable(
                    ErrorKind::IncompatibleTypes,
                    format_code!(
                        "cannot use value of type {} as argument {} to function {}",
                        &passed_type,
                        format!("{}: {}", &defined.name, &defined.typ),
                        &fn_name,
                    )
                    .as_str(),
                    Box::new(original_arg.clone()),
                ));
            }
        }

        RichFnCall {
            fn_name: call.fn_name,
            args: rich_args,
            ret_type,
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
            ctx.add_err(AnalyzeError::new_with_locatable(
                ErrorKind::UnexpectedReturn,
                "cannot return from outside function body",
                Box::new(ret.clone()),
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
                    Some(expected) => {
                        // Skip the type check if either type is unknown. This will be the case if
                        // semantic analysis on either type already failed.
                        if !expected.is_unknown()
                            && !rich_expr.typ.is_unknown()
                            && expected != &rich_expr.typ
                        {
                            ctx.add_err(AnalyzeError::new_with_locatable(
                                ErrorKind::IncompatibleTypes,
                                format_code!(
                                    "cannot return value of type {} from function with return \
                                    type {}",
                                    &rich_expr.typ,
                                    &expected,
                                )
                                .as_str(),
                                Box::new(expr),
                            ));
                        }
                    }
                    None => {
                        ctx.add_err(AnalyzeError::new_with_locatable(
                            ErrorKind::IncompatibleTypes,
                            "cannot return value from function with no return type",
                            Box::new(expr.clone()),
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
                        ctx.add_err(AnalyzeError::new_with_locatable(
                            ErrorKind::IncompatibleTypes,
                            format_code!(
                                "expected return value of type {}, but found empty return",
                                expected,
                            )
                            .as_str(),
                            Box::new(ret),
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
