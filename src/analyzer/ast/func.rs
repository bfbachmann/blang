use std::collections::HashSet;
use std::fmt;
use std::fmt::Formatter;

use crate::analyzer::ast::arg::AArg;
use crate::analyzer::ast::closure::{check_closure_returns, AClosure};
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::ast::tmpl_params::ATmplParams;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::ScopeKind;
use crate::analyzer::type_store::TypeKey;
use crate::parser::ast::func::Function;
use crate::parser::ast::func_sig::FunctionSignature;
use crate::util;

/// Represents a semantically valid function signature.
#[derive(Debug, Clone)]
pub struct AFnSig {
    pub name: String,
    /// The mangled name is the full name of the function that may include information about
    /// it's impl and argument types to disambiguate it from other methods with the same name.
    /// If it's a regular function, this will just be the function name. If it's a member
    /// function, it will be `<type>.<fn_name>`.
    pub mangled_name: String,
    pub args: Vec<AArg>,
    pub maybe_ret_type_key: Option<TypeKey>,
    /// Represents this function signature as a type.
    pub type_key: TypeKey,
    /// The type key of the parent type if this is a member function.
    pub maybe_impl_type_key: Option<TypeKey>,
    /// Optional template parameters (generics) for this function.
    pub tmpl_params: Option<ATmplParams>,
}

impl PartialEq for AFnSig {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && util::vecs_eq(&self.args, &other.args)
            && util::opts_eq(&self.maybe_ret_type_key, &other.maybe_ret_type_key)
            && util::opts_eq(&self.tmpl_params, &other.tmpl_params)
    }
}

impl fmt::Display for AFnSig {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "fn {}(", self.name)?;

        for (i, arg) in self.args.iter().enumerate() {
            write!(f, "{}", arg)?;

            if i != self.args.len() - 1 {
                write!(f, ", ")?;
            }
        }

        if let Some(typ) = &self.maybe_ret_type_key {
            write!(f, "): {}", typ)
        } else {
            write!(f, ")")
        }
    }
}

impl AFnSig {
    /// Analyzes a function signature and returns a semantically valid, type-rich function
    /// signature.
    pub fn from(ctx: &mut ProgramContext, sig: &FunctionSignature) -> Self {
        // If the function has template parameters, we need to analyze them first.
        let tmpl_params = match &sig.tmpl_params {
            Some(params) => Some(ATmplParams::from(ctx, params)),
            None => None,
        };

        // Analyze the arguments.
        let mut args = vec![];
        let mut arg_names = HashSet::new();
        for arg in &sig.args {
            // Make sure the argument name wasn't already used if it's not empty.
            if !arg.name.is_empty() {
                if arg_names.contains(arg.name.as_str()) {
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::DuplicateFnArg,
                        format_code!(
                            "another argument named {} already exists for this function",
                            &arg.name
                        )
                        .as_str(),
                        arg,
                    ));

                    // Skip this invalid argument
                    continue;
                }

                arg_names.insert(arg.name.clone());
            }

            let a_arg = AArg::from(ctx, &arg);
            args.push(a_arg);
        }

        // Analyze the return type.
        let return_type = match &sig.maybe_ret_type {
            Some(typ) => Some(ctx.resolve_type(typ)),
            None => None,
        };

        let maybe_impl_type_key = ctx.get_cur_self_type_key();
        let mut a_fn_sig = AFnSig {
            name: sig.name.to_string(),
            mangled_name: Self::get_mangled_name(ctx, maybe_impl_type_key, sig.name.as_str()),
            args,
            maybe_ret_type_key: return_type,
            type_key: 0, // This will be replaced below after we insert it into the program context.
            maybe_impl_type_key,
            tmpl_params,
        };

        // Add the function as a resolved type to the program context. This is done because
        // functions can be used as variables and therefore need types.
        a_fn_sig.type_key = ctx.insert_type(AType::from_fn_sig(a_fn_sig.clone()));
        ctx.replace_type(a_fn_sig.type_key, AType::from_fn_sig(a_fn_sig.clone()));

        a_fn_sig
    }

    /// Returns the fully qualified name of this function. If it's a regular function, this will
    /// just be the function name. If it's a member function, it will be `<type>.<fn_name>`.
    /// If it's a templated function, argument types and the return type will be appended to the
    /// function name.
    fn get_mangled_name(
        ctx: &ProgramContext,
        maybe_impl_type_key: Option<TypeKey>,
        fn_name: &str,
    ) -> String {
        match maybe_impl_type_key {
            Some(type_key) => {
                let impl_type = ctx.must_get_type(type_key);
                format!("{}.{}", impl_type.name(), fn_name)
            }
            None => ctx.mangle_name(fn_name),
        }
    }

    /// Returns true if this function signature has template parameters.
    pub fn is_templated(&self) -> bool {
        self.tmpl_params.is_some()
    }

    /// Returns true if `other` has arguments of the same type in the same order and the
    /// same return type as `self`.
    pub fn is_same_as(&self, ctx: &ProgramContext, other: &AFnSig) -> bool {
        if self.args.len() != other.args.len() {
            return false;
        }

        for (this_arg, other_arg) in self.args.iter().zip(other.args.iter()) {
            // Skip the more complex arg type check if the type keys already match.
            if this_arg.type_key == other_arg.type_key {
                continue;
            }

            let this_type = ctx.must_get_type(this_arg.type_key);
            let other_type = ctx.must_get_type(other_arg.type_key);
            if !this_type.is_same_as(ctx, other_type, false) {
                return false;
            }
        }

        // Skip the more complex return type check if the return type keys already match.
        if util::opts_eq(&self.maybe_ret_type_key, &other.maybe_ret_type_key) {
            return true;
        }

        let this_ret_type = match &self.maybe_ret_type_key {
            Some(tk) => Some(ctx.must_get_type(*tk)),
            None => None,
        };

        let other_ret_type = match &other.maybe_ret_type_key {
            Some(tk) => Some(ctx.must_get_type(*tk)),
            None => None,
        };

        util::opts_eq(&this_ret_type, &other_ret_type)
    }

    /// Returns a string containing the human-readable version of this function signature.
    /// If `as_type` is true, the function signature will be displayed as a type (without the name
    /// and arg names).
    pub fn display(&self, ctx: &ProgramContext, as_type: bool) -> String {
        let name = if as_type { "" } else { self.name.as_str() };
        let mut s = format!("fn {}(", name);

        for (i, arg) in self.args.iter().enumerate() {
            s += format!("{}", arg.display(ctx, as_type)).as_str();

            if i != self.args.len() - 1 {
                s += format!(", ").as_str();
            }
        }

        if let Some(tk) = &self.maybe_ret_type_key {
            s + format!("): {}", ctx.must_get_type(*tk).display(ctx)).as_str()
        } else {
            s + format!(")").as_str()
        }
    }
}

/// Performs semantic analysis on the function signature, ensuring it doesn't match any other
/// function signature in the ProgramContext.
pub fn analyze_fn_sig(ctx: &mut ProgramContext, sig: &FunctionSignature) {
    // Add the function to the program context with an empty body, making sure it doesn't already
    // exist. We'll replace the function body when we analyze it later.
    let a_fn_sig = AFnSig::from(ctx, &sig);

    if ctx
        .get_defined_fn_sig(None, a_fn_sig.name.as_str())
        .is_some()
        || ctx
            .get_scoped_symbol(None, a_fn_sig.name.as_str())
            .is_some()
    {
        ctx.insert_err(AnalyzeError::new(
            ErrorKind::DuplicateFunction,
            format_code!("{} was already defined", sig.name).as_str(),
            sig,
        ));
    } else {
        ctx.insert_defined_fn_sig(a_fn_sig);
    }
}

/// Represents a semantically valid and type-a function.
#[derive(PartialEq, Debug, Clone)]
pub struct AFn {
    pub signature: AFnSig,
    pub body: AClosure,
}

impl fmt::Display for AFn {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {{...}}", &self.signature)
    }
}

impl AFn {
    /// Performs semantic analysis on the given function and returns an analyzed version of it.
    pub fn from(ctx: &mut ProgramContext, func: &Function) -> Self {
        let signature = AFnSig::from(ctx, &func.signature);

        // Make sure there isn't already another function by the same name. There are already
        // checks for regular function name collisions in `analyze_fn_sig`, but those
        // won't detect nested function name collisions - that's what this is for.
        if ctx.get_fn(None, signature.mangled_name.as_str()).is_some() {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::DuplicateFunction,
                format_code!("{} was already defined", &signature.name).as_str(),
                &func.signature,
            ));
        }

        // Templated functions will be rendered and analyzed when we analyze statements or
        // expressions where they're used. This way, we can use information from the context in
        // which they're used to render and check templated values.
        if func.signature.tmpl_params.is_some() {
            return AFn {
                signature,
                body: AClosure::new_empty(),
            };
        }

        // Analyze the function body.
        let a_closure = AClosure::from(
            ctx,
            &func.body,
            ScopeKind::FnBody(func.signature.name.clone()),
            func.signature.args.clone(),
            func.signature.maybe_ret_type.clone(),
        );

        // Make sure the function return conditions are satisfied by the closure.
        if let Some(ret_type) = &func.signature.maybe_ret_type {
            let a_ret_type = ctx.resolve_type(&ret_type);
            check_closure_returns(
                ctx,
                &a_closure,
                a_ret_type,
                &ScopeKind::FnBody(func.signature.name.clone()),
            );
        }

        AFn {
            signature,
            body: a_closure,
        }
    }

    /// Returns the human-readable version fo this function.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        format!("{} {{...}}", self.signature.display(ctx, false))
    }
}
