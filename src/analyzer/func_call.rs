use std::collections::VecDeque;
use std::fmt;

use colored::Colorize;
use pluralizer::pluralize;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::analyzer::var::RichVar;
use crate::parser::func_call::FunctionCall;
use crate::{format_code, util};

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
