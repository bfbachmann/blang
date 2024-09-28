use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::Formatter;
use std::hash::{Hash, Hasher};

use crate::analyzer::ast::arg::AArg;
use crate::analyzer::ast::closure::{check_closure_returns, AClosure};
use crate::analyzer::ast::params::AParams;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::ScopeKind;
use crate::analyzer::type_store::TypeKey;
use crate::parser::ast::func::Function;
use crate::parser::ast::func_sig::FunctionSignature;
use crate::util;

/// Represents a semantically valid function signature.
#[derive(Debug, Clone, Eq)]
pub struct AFnSig {
    pub name: String,
    /// The mangled name is the full name of the function that may include information about
    /// it to disambiguate it from other functions with the same name.
    pub mangled_name: String,
    pub args: Vec<AArg>,
    pub maybe_ret_type_key: Option<TypeKey>,
    /// Represents this function signature as a type.
    pub type_key: TypeKey,
    /// The type key of the parent type if this is a member function.
    pub maybe_impl_type_key: Option<TypeKey>,
    /// Optional parameters (generics) for this function.
    pub params: Option<AParams>,
}

impl Hash for AFnSig {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.mangled_name.hash(state);
        self.args.hash(state);
        self.maybe_ret_type_key.hash(state);
        self.maybe_impl_type_key.hash(state);
        self.params.hash(state);
    }
}

impl PartialEq for AFnSig {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.mangled_name == other.mangled_name
            && util::vecs_eq(&self.args, &other.args)
            && util::opts_eq(&self.maybe_ret_type_key, &other.maybe_ret_type_key)
            && self.maybe_impl_type_key == other.maybe_impl_type_key
            && util::opts_eq(&self.params, &other.params)
    }
}

impl fmt::Display for AFnSig {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "fn {}(", self.mangled_name)?;

        for (i, arg) in self.args.iter().enumerate() {
            write!(f, "{}", arg)?;

            if i != self.args.len() - 1 {
                write!(f, ", ")?;
            }
        }

        if let Some(typ) = &self.maybe_ret_type_key {
            write!(f, ") -> {}", typ)
        } else {
            write!(f, ")")
        }
    }
}

impl AFnSig {
    /// Analyzes a function signature and returns a semantically valid, type-rich function
    /// signature.
    pub fn from(ctx: &mut ProgramContext, sig: &FunctionSignature) -> Self {
        let maybe_impl_type_key = ctx.get_cur_self_type_key();
        let mangled_name = ctx.mangle_name(None, maybe_impl_type_key, sig.name.as_str(), true);

        // Create a mostly-empty function type and insert it into the program context.
        // We'll fill in the details later, we just need a type key for it now.
        let mut a_fn_sig = AFnSig {
            name: sig.name.to_string(),
            mangled_name,
            args: vec![],
            maybe_ret_type_key: None,
            type_key: ctx.unknown_type_key(),
            maybe_impl_type_key,
            params: None,
        };
        a_fn_sig.type_key = ctx.force_insert_type(AType::from_fn_sig(a_fn_sig.clone()));

        // If the function has generic parameters, we need to analyze them first
        // and store them in the program context. We'll need them when analyzing
        // argument types.
        a_fn_sig.params = match &sig.params {
            Some(params) => {
                let a_params = AParams::from(ctx, params, a_fn_sig.type_key);
                ctx.push_params(a_params.clone());
                Some(a_params)
            }
            None => None,
        };

        // Analyze the arguments.
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
            a_fn_sig.args.push(a_arg);
        }

        // Analyze the return type.
        a_fn_sig.maybe_ret_type_key = match &sig.maybe_ret_type {
            Some(typ) => Some(ctx.resolve_type(typ)),
            None => None,
        };

        // Replace the type now that it has been fully analyzed.
        ctx.replace_type(a_fn_sig.type_key, AType::from_fn_sig(a_fn_sig.clone()));

        // We can clear the params from the program context now that we're
        // done analyzing this signature.
        if a_fn_sig.params.is_some() {
            ctx.pop_params();
        }

        a_fn_sig
    }

    /// Returns true if this function signature has generic parameters.
    pub fn is_parameterized(&self) -> bool {
        self.params.is_some()
    }

    /// Returns true if `other` has arguments of the same type in the same order and the
    /// same return type as `self`.
    pub fn is_same_as(&self, ctx: &ProgramContext, other: &AFnSig) -> bool {
        if self.args.len() != other.args.len() {
            return false;
        }

        for (this_arg, other_arg) in self.args.iter().zip(other.args.iter()) {
            if this_arg.type_key != other_arg.type_key && {
                let this_type = ctx.must_get_type(this_arg.type_key);
                let other_type = ctx.must_get_type(other_arg.type_key);
                !this_type.is_same_as(ctx, other_type, false)
            } {
                return false;
            }
        }

        match (self.maybe_ret_type_key, other.maybe_ret_type_key) {
            (None, None) => true,
            (Some(this_ret_tk), Some(other_ret_tk)) => {
                this_ret_tk == other_ret_tk || {
                    let this_ret_type = ctx.must_get_type(this_ret_tk);
                    let other_ret_type = ctx.must_get_type(other_ret_tk);
                    this_ret_type.is_same_as(ctx, other_ret_type, false)
                }
            }
            _ => false,
        }
    }

    /// Updates this function signature by replacing any instances of the
    /// `Self`  type inside it with `replacement_type_key`. Also
    /// records the new function signature as a new type in the program context.
    pub fn replace_self_type_and_define(
        &mut self,
        ctx: &mut ProgramContext,
        replacement_type_key: TypeKey,
    ) {
        fn replace_tk(
            ctx: &mut ProgramContext,
            tk: &mut TypeKey,
            target_tk: TypeKey,
            replacement_tk: TypeKey,
        ) {
            if *tk == target_tk {
                *tk = replacement_tk;
                return;
            }

            if let Some(new_tk) =
                ctx.monomorphize_type(*tk, &HashMap::from([(target_tk, replacement_tk)]))
            {
                *tk = new_tk;
            }
        }

        let self_type_key = ctx.self_type_key();

        // Make type key replacements in the function signature.
        for arg in &mut self.args {
            replace_tk(ctx, &mut arg.type_key, self_type_key, replacement_type_key)
        }

        if let Some(ret_tk) = &mut self.maybe_ret_type_key {
            replace_tk(ctx, ret_tk, self_type_key, replacement_type_key);
        }

        if let Some(impl_tk) = &mut self.maybe_impl_type_key {
            replace_tk(ctx, impl_tk, self_type_key, replacement_type_key);
        }

        // Re-mangle the name based on the updated type info.
        self.mangled_name =
            ctx.mangle_name(None, self.maybe_impl_type_key, self.name.as_str(), true);

        // Define the new type in the program context.
        let new_fn_type_key = ctx.insert_type(AType::Function(Box::new(self.clone())));
        self.type_key = new_fn_type_key;
        ctx.replace_type(new_fn_type_key, AType::Function(Box::new(self.clone())));
    }

    /// Returns a string containing the human-readable version of this function signature.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        let name = self.name.as_str();
        let mut s = format!("fn {}", name);

        if let Some(params) = &self.params {
            s += params.display(ctx).as_str();
        }

        s += "(";

        for (i, arg) in self.args.iter().enumerate() {
            if i == 0 {
                s += format!("{}", arg.display(ctx)).as_str();
            } else {
                s += format!(", {}", arg.display(ctx)).as_str();
            }
        }

        s += ")";

        if let Some(tk) = &self.maybe_ret_type_key {
            s += format!(": {}", ctx.display_type(*tk)).as_str();
        }

        s
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
            format_code!("{} is already defined", sig.name).as_str(),
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
        // If the function signature has already been analyzed, there is no need
        // to re-analyze it. This will be the case for regular functions defined
        // at the top level of the module. It will not be the case for nested
        // functions and methods.
        let signature = match ctx.get_defined_fn_sig(None, func.signature.name.as_str()) {
            Some(sig) if ctx.get_cur_self_type_key().is_none() => sig.clone(),
            _ => AFnSig::from(ctx, &func.signature),
        };

        // Make sure there isn't already another function by the same name. There are already
        // checks for regular function name collisions in `analyze_fn_sig`, but those
        // won't detect nested function name collisions - that's what this is for.
        if ctx.get_fn(None, signature.mangled_name.as_str()).is_some() {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::DuplicateFunction,
                format_code!("{} is already defined", &signature.name).as_str(),
                &func.signature,
            ));
        }

        // Before we analyze the function body, we'll define the function
        // signature parameters in the program context so they can be resolved
        // during function body analysis.
        if let Some(params) = &signature.params {
            ctx.push_params(params.clone());
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
        if func.signature.maybe_ret_type.is_some() {
            check_closure_returns(
                ctx,
                &a_closure,
                &ScopeKind::FnBody(func.signature.name.clone()),
            );
        }

        // Record the function name as public in the current module if necessary.
        if func.is_pub {
            if let Some(type_key) = ctx.get_cur_self_type_key() {
                ctx.insert_pub_member_fn_name(type_key, func.signature.name.as_str());
            } else {
                ctx.insert_pub_fn_name(func.signature.name.as_str());
            }
        }

        // Remove the function signature params now that we're done analyzing
        // the function.
        if signature.params.is_some() {
            ctx.pop_params();
        }

        AFn {
            signature,
            body: a_closure,
        }
    }

    /// Returns the human-readable version fo this function.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        format!("{} {{ ... }}", self.signature.display(ctx))
    }
}
