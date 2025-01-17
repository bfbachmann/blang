use crate::analyzer::ast::arg::AArg;
use crate::analyzer::ast::closure::{check_closure_returns, AClosure};
use crate::analyzer::ast::params::AParams;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::ScopeKind;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::Span;
use crate::parser::ast::func::Function;
use crate::parser::ast::func_sig::FunctionSignature;
use crate::util;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::Formatter;
use std::hash::{Hash, Hasher};

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
    pub fn from(ctx: &mut ProgramContext, sig: &FunctionSignature) -> AFnSig {
        // Only try to determine if this is a method on a type (i.e. it has a spec and impl
        // type key) if it's a named function signature.
        let is_anon = sig.name.is_empty();
        let maybe_impl_type_key = match is_anon {
            true => None,
            false => ctx.get_cur_self_type_key(),
        };
        let maybe_spec_type_key = match is_anon {
            true => None,
            false => ctx.get_cur_spec_type_key(),
        };

        // Mangle the function name so it's unique.
        let mangled_name = ctx.mangle_name(
            None,
            maybe_impl_type_key,
            maybe_spec_type_key,
            sig.name.as_str(),
            true,
        );

        // If this function signature has a name, we can try to locate it by its mangled name to
        // avoid re-analyzing it.
        if !is_anon {
            if let Some(fn_sig) = ctx.get_fn_sig_by_mangled_name(None, mangled_name.as_str()) {
                return fn_sig.clone();
            }
        }

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
        for (i, arg) in sig.args.iter().enumerate() {
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

                if arg.name == "self" {
                    if ctx.get_cur_self_type_key().is_none() {
                        ctx.insert_err(AnalyzeError::new(
                            ErrorKind::IllegalSelfArg,
                            format_code!(
                                "cannot declare argument {} outside of {} or {} block",
                                "self",
                                "spec",
                                "impl"
                            )
                            .as_str(),
                            arg,
                        ));

                        // Skip this invalid argument
                        continue;
                    } else if i != 0 {
                        ctx.insert_err(AnalyzeError::new(
                            ErrorKind::IllegalSelfArg,
                            format!("{} must always be the first argument, if present", "self",)
                                .as_str(),
                            arg,
                        ));

                        // Skip this invalid argument
                        continue;
                    }
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

        // Track the function type by name in the current module, if it has a name. We do this
        // so we can avoid reanalyzing it in the future.
        if !a_fn_sig.name.is_empty() {
            ctx.insert_fn_sig(a_fn_sig.mangled_name.as_str(), a_fn_sig.type_key);
        }

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
                let this_type = ctx.get_type(this_arg.type_key);
                let other_type = ctx.get_type(other_arg.type_key);
                !this_type.is_same_as(ctx, other_type, false)
            } {
                return false;
            }
        }

        match (self.maybe_ret_type_key, other.maybe_ret_type_key) {
            (None, None) => true,
            (Some(this_ret_tk), Some(other_ret_tk)) => {
                this_ret_tk == other_ret_tk || {
                    let this_ret_type = ctx.get_type(this_ret_tk);
                    let other_ret_type = ctx.get_type(other_ret_tk);
                    this_ret_type.is_same_as(ctx, other_ret_type, false)
                }
            }
            _ => false,
        }
    }

    /// Returns true only if `self` is a valid implementation of `other`. This is supposed to be
    /// used to check if member function `self` correctly implements member function `other` from a
    /// spec.
    pub fn implements(&self, ctx: &mut ProgramContext, other: &AFnSig) -> bool {
        if self.args.len() != other.args.len()
            || self.maybe_ret_type_key.is_some() != other.maybe_ret_type_key.is_some()
        {
            return false;
        }

        match (&self.params, &other.params) {
            (Some(these_params), Some(other_params)) => {
                if these_params.params.len() != other_params.params.len() {
                    return false;
                }

                // Check that the params are compatible.
                let mut type_mappings = HashMap::new();
                for (this_param, other_param) in
                    these_params.params.iter().zip(other_params.params.iter())
                {
                    let this_param_type =
                        ctx.get_type(this_param.generic_type_key).to_generic_type();
                    let other_param_type =
                        ctx.get_type(other_param.generic_type_key).to_generic_type();

                    if this_param_type.spec_type_keys.len() != other_param_type.spec_type_keys.len()
                    {
                        return false;
                    }

                    for (this_spec_tk, other_spec_tk) in this_param_type
                        .spec_type_keys
                        .iter()
                        .zip(other_param_type.spec_type_keys.iter())
                    {
                        if this_spec_tk != other_spec_tk {
                            return false;
                        }
                    }

                    type_mappings.insert(this_param.generic_type_key, other_param.generic_type_key);
                }

                // At this point we know the generic params are compatible, so we can replace
                // all generic param type keys in this function signature with those of the other
                // and see if the resulting signature match matches `other`.
                let mut this = self.clone();
                this.replace_types(ctx, &type_mappings);
                return this.is_same_as(ctx, &other);
            }

            (None, None) => {}

            _ => return false,
        }

        return self.is_same_as(ctx, other);
    }

    /// Updates this function signature by replacing any instances of the
    /// `target_type_key` inside it with `replacement_type_key`. Also records
    /// the new function signature as a new type in the program context.
    pub fn replace_type_and_define(
        &mut self,
        ctx: &mut ProgramContext,
        target_type_key: TypeKey,
        replacement_type_key: TypeKey,
    ) {
        self.replace_types(
            ctx,
            &HashMap::from([(target_type_key, replacement_type_key)]),
        );

        // Define the new type in the program context.
        let new_fn_type_key = ctx.insert_type(AType::Function(Box::new(self.clone())));
        self.type_key = new_fn_type_key;
        ctx.replace_type(new_fn_type_key, AType::Function(Box::new(self.clone())));
    }

    /// Replaces type keys in `self` using `type_mappings`.
    fn replace_types(
        &mut self,
        ctx: &mut ProgramContext,
        type_mappings: &HashMap<TypeKey, TypeKey>,
    ) {
        fn replace_tk(
            ctx: &mut ProgramContext,
            tk: &mut TypeKey,
            type_mappings: &HashMap<TypeKey, TypeKey>,
        ) {
            if let Some(replacement_tk) = type_mappings.get(tk) {
                *tk = *replacement_tk;
                return;
            }

            if let Some(new_tk) = ctx.monomorphize_type(*tk, type_mappings) {
                *tk = new_tk;
            }
        }

        // Make type key replacements in the function signature.
        for arg in &mut self.args {
            replace_tk(ctx, &mut arg.type_key, type_mappings)
        }

        if let Some(ret_tk) = &mut self.maybe_ret_type_key {
            replace_tk(ctx, ret_tk, type_mappings);
        }

        if let Some(impl_tk) = &mut self.maybe_impl_type_key {
            replace_tk(ctx, impl_tk, type_mappings);
        }

        // Re-mangle the name based on the updated type info.
        // TODO: Not sure this is right for all cases.
        self.mangled_name = ctx.remangle_name(
            self.mangled_name.as_str(),
            self.maybe_impl_type_key.unwrap(),
        );
    }

    /// Returns a string containing the human-readable version of this function signature.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        let mut s = match self.name.starts_with("anon_fn::") {
            true => "fn ".to_string(),
            false => {
                format!("fn {}", self.name)
            }
        };

        if let Some(params) = &self.params {
            s += params.display(ctx).as_str();
        }

        s += "(";

        for (i, arg) in self.args.iter().enumerate() {
            let arg_display = arg.display(ctx);
            if i == 0 {
                s += format!("{}", arg_display).as_str();
            } else {
                s += format!(", {}", arg_display).as_str();
            }
        }

        s += ")";

        if let Some(tk) = &self.maybe_ret_type_key {
            s += format!(" -> {}", ctx.display_type(*tk)).as_str();
        }

        s
    }
}

/// Performs semantic analysis on the function signature, ensuring it doesn't match any other
/// function signature in the ProgramContext.
pub fn analyze_fn_sig(ctx: &mut ProgramContext, sig: &FunctionSignature) {
    // Add the function to the program context with an empty body, making sure it doesn't already
    // exist. We'll replace the function body when we analyze it later.
    let mangled_name = ctx.mangle_name(None, None, None, sig.name.as_str(), true);
    if ctx
        .get_fn_sig_by_mangled_name(None, mangled_name.as_str())
        .is_some()
        || ctx.get_scoped_symbol(None, sig.name.as_str()).is_some()
    {
        ctx.insert_err(AnalyzeError::new(
            ErrorKind::DuplicateFunction,
            format_code!("{} is already defined", sig.name).as_str(),
            sig,
        ));
        return;
    }

    AFnSig::from(ctx, &sig);
}

/// Represents a semantically valid and type-a function.
#[derive(PartialEq, Debug, Clone)]
pub struct AFn {
    pub signature: AFnSig,
    pub body: AClosure,
    pub span: Span,
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
                format_code!("function {} is already defined", &signature.name).as_str(),
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
            if ctx.get_cur_self_type_key().is_none() {
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
            span: func.span,
        }
    }

    /// Returns the human-readable version fo this function.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        format!("{} {{ ... }}", self.signature.display(ctx))
    }
}
