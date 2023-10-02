use std::fmt;
use std::fmt::Formatter;

use colored::Colorize;

use crate::analyzer::arg::RichArg;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::{RichType, TypeId};
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
