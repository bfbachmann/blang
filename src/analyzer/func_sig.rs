use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::Formatter;

use colored::Colorize;

use crate::analyzer::arg::RichArg;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::analyzer::tmpl_params::RichTmplParams;
use crate::parser::func_sig::FunctionSignature;
use crate::parser::r#type::Type;
use crate::{format_code, util};

/// Represents a semantically valid function signature.
#[derive(Debug, Clone)]
pub struct RichFnSig {
    pub name: String,
    pub args: Vec<RichArg>,
    pub ret_type_id: Option<TypeId>,
    /// Represents this function signature as a type.
    pub type_id: TypeId,
    /// The type ID of the parent type if this is a member function.
    pub impl_type_id: Option<TypeId>,
    /// Optional template parameters (generics) for this function.
    pub tmpl_params: Option<RichTmplParams>,
}

impl PartialEq for RichFnSig {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && util::vecs_eq(&self.args, &other.args)
            && util::opts_eq(&self.ret_type_id, &other.ret_type_id)
            && util::opts_eq(&self.tmpl_params, &other.tmpl_params)
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
        // If the function has template parameters, we need to analyze them first.
        let mut type_ids_to_delete = vec![];
        let tmpl_params = match &sig.tmpl_params {
            Some(params) => {
                let tmpl_params = RichTmplParams::from(ctx, params);

                // Add the template params to the program context as the current function template
                // params. This way, the type analyzer can look them up when resolving templated
                // types for this function signature.
                for param in &tmpl_params.params {
                    let param_type_id = param.get_type_id();
                    ctx.add_resolved_type(
                        param_type_id.clone(),
                        RichType::Templated(param.clone()),
                    );
                    type_ids_to_delete.push(param_type_id);
                }

                Some(tmpl_params)
            }
            None => None,
        };

        // Analyze the arguments.
        let mut args = vec![];
        let mut arg_names = HashSet::new();
        for arg in &sig.args {
            // Make sure the argument name wasn't already used if it's not empty.
            if !arg.name.is_empty() {
                if arg_names.contains(arg.name.as_str()) {
                    ctx.add_err(AnalyzeError::new(
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
        let impl_type_id = match ctx.get_this_type_id() {
            Some(type_id) => Some(type_id.clone()),
            None => None,
        };

        let rich_fn_sig = RichFnSig {
            name: sig.name.to_string(),
            args,
            ret_type_id: return_type,
            type_id: TypeId::from(Type::Function(Box::new(sig.clone()))),
            impl_type_id,
            tmpl_params,
        };

        // Add the function as a resolved type to the program context. This is done because
        // functions can be used as variables and therefore need types.
        let type_id = TypeId::from(Type::Function(Box::new(sig.clone())));
        ctx.add_resolved_type(type_id, RichType::from_fn_sig(rich_fn_sig.clone()));

        // Drop the function template parameters now that we're done analyzing the function
        // signature.
        for type_id in type_ids_to_delete {
            ctx.remove_resolved_type(&type_id);
        }

        rich_fn_sig
    }

    /// Returns the fully qualified name of this function. If it's a regular function, this will
    /// just be the function name. If it's a member function, it will be `<type>.<fn_name>`.
    /// If it's a templated function, argument types and the return type will be appended to the
    /// function name.
    pub fn full_name(&self) -> String {
        let mut full_name = match &self.impl_type_id {
            Some(type_id) => format!("{}.{}", type_id.to_string(), self.name),
            None => self.name.to_string(),
        };

        if self.is_templated() {
            for arg in &self.args {
                full_name = format!("{},{}", full_name, arg.type_id.to_string().as_str());
            }

            if let Some(id) = &self.ret_type_id {
                full_name = format!("{}~{}", full_name, id);
            }
        }

        full_name
    }

    /// Returns true if the function signature has `this` as its first argument.
    pub fn takes_this(&self) -> bool {
        match self.args.first() {
            Some(arg) => arg.name == "this",
            None => false,
        }
    }

    /// Returns true if this function signature has template parameters.
    pub fn is_templated(&self) -> bool {
        self.tmpl_params.is_some()
    }

    /// Returns true if `other` has arguments of the same type in the same order and the
    /// same return type as `self`. `remapped_type_ids` will be used to convert type IDs from
    /// `other` before checks are performed.
    pub fn is_same_as(
        &self,
        other: &RichFnSig,
        remapped_type_ids: &HashMap<TypeId, TypeId>,
    ) -> bool {
        if self.args.len() != other.args.len() {
            return false;
        }

        for (a, b) in self.args.iter().zip(other.args.iter()) {
            // Replace type IDs for b using the provided mapping.
            let b_type_id = match remapped_type_ids.get(&b.type_id) {
                Some(replacement_id) => replacement_id,
                None => &b.type_id,
            };

            if &a.type_id != b_type_id {
                return false;
            }
        }

        // Replace the return type of `other` using the provided mapping.
        let other_ret_type_id = match &other.ret_type_id {
            Some(id) => match remapped_type_ids.get(id) {
                Some(replacement_id) => Some(replacement_id.clone()),
                None => Some(id.clone()),
            },
            None => None,
        };

        util::opts_eq(&self.ret_type_id, &other_ret_type_id)
    }
}

/// Performs semantic analysis on the function signature, ensuring it doesn't match any other
/// function signature in the ProgramContext.
pub fn analyze_fn_sig(ctx: &mut ProgramContext, sig: &FunctionSignature) -> RichFnSig {
    // Add the function to the program context with an empty body, making sure it doesn't already
    // exist. We'll replace the function body when we analyze it later.
    let rich_fn_sig = RichFnSig::from(ctx, &sig);
    if ctx.add_extern_fn(rich_fn_sig.clone()).is_some() {
        ctx.add_err(AnalyzeError::new(
            ErrorKind::DuplicateFunction,
            format_code!("function {} was already defined in this scope", sig.name).as_str(),
            sig,
        ));
    }

    rich_fn_sig
}
