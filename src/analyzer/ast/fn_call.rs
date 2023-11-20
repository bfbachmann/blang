use std::collections::VecDeque;
use std::fmt;

use colored::Colorize;
use pluralizer::pluralize;

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::func::AFnSig;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::symbol::ASymbol;
use crate::analyzer::error::{AnalyzeError, AnalyzeResult, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::parser::func_call::FunctionCall;
use crate::{format_code, util};

/// Represents a fully type-resolved and analyzed function call.
#[derive(Clone, Debug)]
pub struct AFnCall {
    pub fn_symbol: ASymbol,
    pub args: Vec<AExpr>,
    pub maybe_ret_type_key: Option<TypeKey>,
}

impl fmt::Display for AFnCall {
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

impl PartialEq for AFnCall {
    fn eq(&self, other: &Self) -> bool {
        self.fn_symbol == other.fn_symbol
            && util::vecs_eq(&self.args, &other.args)
            && util::opts_eq(&self.maybe_ret_type_key, &other.maybe_ret_type_key)
    }
}

impl AFnCall {
    /// Analyzes the given function call and returns a type-rich version of it.
    pub fn from(ctx: &mut ProgramContext, call: &FunctionCall) -> Self {
        // Calls to "main" should not be allowed.
        if call.has_fn_name("main") {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::CallToMain,
                "cannot call entrypoint main",
                call,
            ));
        }

        // Extract type information from args.
        let mut passed_args: VecDeque<AExpr> = call
            .args
            .iter()
            .map(|arg| AExpr::from(ctx, arg.clone(), None, true))
            .collect();

        // Get the type key of the first argument so we can pass it as a hint to the variable
        // resolver. The variable resolver can use it as a means of locating member functions
        // for types. This is necessary for chained method calls.
        let maybe_impl_type_key = match passed_args.front() {
            Some(arg) => Some(arg.type_key),
            None => None,
        };

        // Make sure the function exists, either as a fully analyzed function, an external function
        // signature, or a variable.
        let a_fn_symbol = ASymbol::from(ctx, &call.fn_symbol, true, maybe_impl_type_key);
        let var_type = ctx.must_get_type(a_fn_symbol.get_type_key());

        // If the function symbol failed analysis, we can return early.
        if var_type.is_unknown() {
            return AFnCall {
                fn_symbol: a_fn_symbol,
                args: vec![],
                maybe_ret_type_key: Some(ctx.unknown_type_key()),
            };
        }

        // Try to locate the function signature for this function call. If it's a call to a type
        // member function, we'll look up the function using the type key. Otherwise, we just extract
        // the function signature from the variable type, as it should be a function type.
        let fn_sig = match AFnCall::get_fn_sig(ctx, &a_fn_symbol, &call) {
            Ok(sig) => sig,
            Err(err) => {
                ctx.insert_err(err);

                return AFnCall {
                    fn_symbol: a_fn_symbol,
                    args: vec![],
                    maybe_ret_type_key: Some(ctx.unknown_type_key()),
                };
            }
        };

        // Clone here to avoid borrow issues.
        let fn_sig = fn_sig.clone();
        let maybe_ret_type_key = fn_sig.ret_type_key.clone();

        // If this function takes the special argument `self` and was not called directly via its
        // fully-qualified name, add the special `self` argument.
        let maybe_self = a_fn_symbol.clone().without_last_member();
        let called_on_self = fn_sig.maybe_impl_type_key.is_some()
            && maybe_self.get_type_key() == fn_sig.maybe_impl_type_key.unwrap()
            && !a_fn_symbol.is_type;

        // If the function call is to an instance method, make sure the method takes `self` as its
        // first argument.
        if called_on_self && a_fn_symbol.is_method() {
            if fn_sig.takes_self() {
                // Add `self` as the first argument since the method is being called on it.
                passed_args.push_front(AExpr::from_symbol(maybe_self));
            } else {
                // This is a call to a method that does not take `self` as its first argument.
                ctx.insert_err(
                    AnalyzeError::new(
                        ErrorKind::UndefMember,
                        format_code!(
                            "cannot call function {} on value of type {}",
                            fn_sig.name,
                            ctx.display_type_for_key(maybe_self.get_type_key()),
                        )
                        .as_str(),
                        call,
                    )
                    .with_detail(
                        format_code!(
                            "Member function {} on type {} does not take {} as its first argument.",
                            fn_sig.display(ctx),
                            fn_sig.maybe_impl_type_key.unwrap(),
                            "self",
                        )
                        .as_str(),
                    )
                    .with_help(
                        format_code!("Did you mean to call {}?", fn_sig.full_name()).as_str(),
                    ),
                );

                return AFnCall {
                    fn_symbol: a_fn_symbol,
                    args: vec![],
                    maybe_ret_type_key,
                };
            }
        }

        // Make sure the right number of arguments were passed.
        if passed_args.len() != fn_sig.args.len() {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::WrongNumberOfArgs,
                format!(
                    "{} expects {}, but {} provided",
                    format_code!(fn_sig.display(ctx)),
                    pluralize("argument", fn_sig.args.len() as isize, true),
                    pluralize("was", passed_args.len() as isize, true)
                )
                .as_str(),
                call,
            ));

            return AFnCall {
                fn_symbol: a_fn_symbol,
                args: passed_args.into(),
                maybe_ret_type_key,
            };
        }

        // If the function is templated, try render it. The rendered function will be placed
        // inside the program context.
        if fn_sig.is_templated() {
            todo!();
        } else {
            // Make sure the arguments are of the right types.
            for (passed_arg, defined_arg) in passed_args.iter().zip(fn_sig.args.iter()) {
                // Try coerce the passed expression to the right type before performing the type
                // check.
                let passed_arg = passed_arg.clone().try_coerce_to(ctx, defined_arg.type_key);

                // Skip the check if the argument type is unknown. This will happen if the argument
                // already failed semantic analysis.
                let passed_type = ctx.must_get_type(passed_arg.type_key);
                if passed_type.is_unknown() {
                    continue;
                }

                let defined_type = ctx.must_get_type(defined_arg.type_key);
                if !passed_type.is_same_as(ctx, &defined_type) {
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::MismatchedTypes,
                        format_code!(
                            "cannot use value of type {} as argument {} to {}",
                            passed_type.display(ctx),
                            defined_arg.display(ctx),
                            fn_sig.display(ctx),
                        )
                        .as_str(),
                        call,
                    ));
                }
            }
        }

        AFnCall {
            fn_symbol: a_fn_symbol,
            args: passed_args.into(),
            maybe_ret_type_key,
        }
    }

    /// Resolves the function signature for the given call.
    fn get_fn_sig<'a>(
        ctx: &'a mut ProgramContext,
        a_fn_symbol: &'a ASymbol,
        call: &FunctionCall,
    ) -> AnalyzeResult<&'a AFnSig> {
        if a_fn_symbol.is_type {
            let method_name = a_fn_symbol.get_last_member_name();
            match ctx.get_member_fn(a_fn_symbol.parent_type_key, method_name.as_str()) {
                Some(fn_sig) => Ok(fn_sig),
                None => Err(AnalyzeError::new(
                    ErrorKind::UndefMember,
                    format_code!(
                        "type {} has no member function {}",
                        a_fn_symbol.name,
                        method_name
                    )
                    .as_str(),
                    call,
                )),
            }
        } else {
            match ctx.must_get_type(a_fn_symbol.get_type_key()) {
                AType::Function(fn_sig) => Ok(fn_sig),
                other => {
                    // The value being used here is not a function.
                    Err(AnalyzeError::new(
                        ErrorKind::MismatchedTypes,
                        format_code!("type {} is not callable", other.display(ctx)).as_str(),
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

    /// Returns the human-readable version of this function call.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        let mut s = format!("{}(", self.fn_symbol);

        for (i, arg) in self.args.iter().enumerate() {
            s += format!("{}", arg.display(ctx)).as_str();

            if i < self.args.len() - 1 {
                s += format!(", ").as_str();
            }
        }

        s + format!(")").as_str()
    }
}
