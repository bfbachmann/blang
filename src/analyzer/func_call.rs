use std::collections::VecDeque;
use std::fmt;

use colored::Colorize;
use pluralizer::pluralize;

use crate::analyzer::error::{AnalyzeError, AnalyzeResult, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::func::RichFn;
use crate::analyzer::func_sig::RichFnSig;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::analyzer::symbol::RichSymbol;
use crate::parser::func_call::FunctionCall;
use crate::{format_code, util};

/// Represents a fully type-resolved and analyzed function call.
#[derive(Clone, Debug)]
pub struct RichFnCall {
    pub fn_symbol: RichSymbol,
    pub args: Vec<RichExpr>,
    pub maybe_ret_type_id: Option<TypeId>,
}

impl fmt::Display for RichFnCall {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}(", self.fn_symbol)?;

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
        self.fn_symbol == other.fn_symbol
            && util::vecs_eq(&self.args, &other.args)
            && util::opts_eq(&self.maybe_ret_type_id, &other.maybe_ret_type_id)
    }
}

impl RichFnCall {
    /// Analyzes the given function call and returns a type-rich version of it.
    pub fn from(ctx: &mut ProgramContext, call: FunctionCall) -> Self {
        // Calls to "main" should not be allowed.
        if call.has_fn_name("main") {
            ctx.add_err(AnalyzeError::new(
                ErrorKind::CallToMain,
                "cannot call entrypoint main",
                &call,
            ));
        }

        // Extract type information from args.
        let mut passed_args: VecDeque<RichExpr> = call
            .args
            .iter()
            .map(|arg| RichExpr::from(ctx, arg.clone(), None))
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
        let mut rich_fn_symbol = RichSymbol::from(ctx, &call.fn_symbol, true, maybe_impl_type_id);
        let var_type = ctx
            .get_resolved_type(rich_fn_symbol.get_type_id())
            .unwrap()
            .clone();

        // If the function symbol failed analysis, we can return early.
        if var_type.is_unknown() {
            return RichFnCall {
                fn_symbol: rich_fn_symbol,
                args: vec![],
                maybe_ret_type_id: Some(TypeId::unknown()),
            };
        }

        // Try to locate the function signature for this function call. If it's a call to a type
        // member function, we'll look up the function using the type ID. Otherwise, we just extract
        // the function signature from the variable type, as it should be a function type.
        let fn_sig = match RichFnCall::get_fn_sig(ctx, &rich_fn_symbol, &call, &var_type) {
            Ok(sig) => sig,
            Err(err) => {
                ctx.add_err(err);

                return RichFnCall {
                    fn_symbol: rich_fn_symbol,
                    args: vec![],
                    maybe_ret_type_id: Some(TypeId::unknown()),
                };
            }
        };

        // Clone here to avoid borrow issues.
        let mut fn_sig = fn_sig.clone();
        let mut maybe_ret_type_id = fn_sig.ret_type_id.clone();

        // If this function takes the special argument `this` and was not called directly via its
        // fully-qualified name, add the special `this` argument.
        let maybe_this = rich_fn_symbol.clone().without_last_member();
        let called_on_this = fn_sig.impl_type_id.is_some()
            && maybe_this.get_type_id() == fn_sig.impl_type_id.as_ref().unwrap()
            && !rich_fn_symbol.is_type;

        // If the function call is to an instance method, make sure the method takes `this` as its
        // first argument.
        if called_on_this && rich_fn_symbol.is_method() {
            if fn_sig.takes_this() {
                // Add `this` as the first argument since the method is being called on it.
                passed_args.push_front(RichExpr::from_symbol(maybe_this));
            } else {
                // This is a call to a method that does not take `this` as its first argument.
                ctx.add_err(
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
                    .with_help(
                        format_code!("Did you mean to call {}?", fn_sig.full_name()).as_str(),
                    ),
                );

                return RichFnCall {
                    fn_symbol: rich_fn_symbol,
                    args: vec![],
                    maybe_ret_type_id,
                };
            }
        }

        // Make sure the right number of arguments were passed.
        if passed_args.len() != fn_sig.args.len() {
            ctx.add_err(AnalyzeError::new(
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

            return RichFnCall {
                fn_symbol: rich_fn_symbol,
                args: passed_args.into(),
                maybe_ret_type_id,
            };
        }

        // If the function is templated, try render it. The rendered function will be placed
        // inside the program context.
        if fn_sig.is_templated() {
            let func = ctx
                .get_templated_fn(fn_sig.full_name().as_str())
                .unwrap()
                .clone();
            if let Err(mut err) = RichFn::render(ctx, &mut fn_sig, func, &passed_args) {
                // We failed to render the function being called, so we should update the error,
                // store it, and return a placeholder function call.
                err.start_pos = call.start_pos.clone();
                err.end_pos = call.end_pos.clone();
                ctx.add_err(err);

                return RichFnCall {
                    fn_symbol: rich_fn_symbol,
                    args: vec![],
                    maybe_ret_type_id,
                };
            }

            // Update the function symbol name to match the rendered function name.
            rich_fn_symbol.set_last_member_name(fn_sig.full_name().as_str());

            // Update the type ID of the symbol to point to the rendered function.
            rich_fn_symbol.set_type_id(fn_sig.type_id);

            // Update the return type ID to be the new rendered type ID.
            maybe_ret_type_id = fn_sig.ret_type_id;
        } else {
            // Make sure the arguments are of the right types.
            let passed_arg_type_ids: Vec<&TypeId> =
                passed_args.iter().map(|a| &a.type_id).collect();
            for (passed_type_id, defined) in passed_arg_type_ids.into_iter().zip(fn_sig.args.iter())
            {
                // Skip the check if the argument type is unknown. This will happen if the argument
                // already failed semantic analysis.
                if ctx.must_get_resolved_type(passed_type_id).is_unknown() {
                    continue;
                }

                if passed_type_id != &defined.type_id {
                    ctx.add_err(AnalyzeError::new(
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
        }

        RichFnCall {
            fn_symbol: rich_fn_symbol,
            args: passed_args.into(),
            maybe_ret_type_id,
        }
    }

    /// Resolves the function signature for the given call.
    fn get_fn_sig<'a>(
        ctx: &'a mut ProgramContext,
        rich_fn_symbol: &'a RichSymbol,
        call: &FunctionCall,
        var_type: &'a RichType,
    ) -> AnalyzeResult<&'a RichFnSig> {
        if rich_fn_symbol.is_type {
            let method_name = rich_fn_symbol.get_last_member_name();
            match ctx.get_type_member_fn(&rich_fn_symbol.parent_type_id, method_name.as_str()) {
                Some(fn_sig) => Ok(fn_sig),
                None => Err(AnalyzeError::new(
                    ErrorKind::MemberNotDefined,
                    format_code!(
                        "type {} has no member function {}",
                        rich_fn_symbol.name,
                        method_name
                    )
                    .as_str(),
                    call,
                )),
            }
        } else {
            match var_type {
                RichType::Function(fn_sig) => Ok(fn_sig),
                other => {
                    // The value being used here is not a function.
                    Err(AnalyzeError::new(
                        ErrorKind::MismatchedTypes,
                        format_code!("type {} is not callable", other).as_str(),
                        call,
                    ))
                }
            }
        }
    }

    /// Returns true if this is a method call (either on a type or an instance).
    pub fn is_method_call(&self) -> bool {
        self.fn_symbol.is_method()
    }
}
