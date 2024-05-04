use std::fmt;
use std::fmt::{Display, Formatter};

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::scope::ScopedSymbol;
use crate::analyzer::type_store::TypeKey;
use crate::parser::ast::r#const::Const;
use crate::parser::ast::r#type::Type;
use crate::{format_code, util};

/// Represents a semantically valid constant declaration.
#[derive(Debug, Clone)]
pub struct AConst {
    pub name: String,
    pub declared_type_key: Option<TypeKey>,
    pub value: AExpr,
}

impl PartialEq for AConst {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && util::opts_eq(&self.declared_type_key, &other.declared_type_key)
            && self.value == other.value
    }
}

impl Display for AConst {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.name)?;

        if let Some(typ) = &self.declared_type_key {
            write!(f, ": {}", typ)?;
        }

        write!(f, " = {}", self.value)
    }
}

impl AConst {
    /// Analyzes a const declaration and returns a semantically valid, type-rich constant
    /// declaration.
    pub fn from(ctx: &mut ProgramContext, const_decl: &Const) -> Self {
        // Analyze the optional constant type.
        let declared_tk = match &const_decl.maybe_type {
            Some(typ) => Some(ctx.resolve_type(typ)),
            None => None,
        };

        // Make sure the constant value is a valid constant.
        let value = AExpr::from(
            ctx,
            const_decl.value.clone(),
            declared_tk,
            false,
            false,
            false,
        );

        // Add the symbol to the program context so it can be used later.
        ctx.insert_symbol(ScopedSymbol::new_const(
            const_decl.name.as_str(),
            value.type_key,
        ));

        // Just return a dummy value if the expression already failed analysis.
        if ctx.must_get_type(value.type_key).is_unknown() {
            return AConst::new_zero_value(ctx, const_decl.name.as_str());
        }

        // Error if the value assigned to the constant is not constant.
        if !value.kind.is_const() {
            ctx.insert_err(
                AnalyzeError::new(
                    ErrorKind::InvalidConst,
                    format_code!("{} is not a constant", value.display(ctx)).as_str(),
                    &const_decl.value,
                )
                .with_detail("Constant expressions cannot contain variables or function calls."),
            );

            return AConst::new_zero_value(ctx, const_decl.name.as_str());
        }

        // Store the constant value in the program context so we can use it when we've evaluating
        // constant expressions at compile time.
        ctx.insert_const_value(const_decl.name.as_str(), value.clone());

        // Record the constant as a public value in this module if necessary.
        if const_decl.is_pub {
            ctx.insert_pub_const_name(const_decl.name.as_str());
        }

        AConst {
            name: const_decl.name.clone(),
            declared_type_key: declared_tk,
            value,
        }
    }

    /// Creates a new constant with the given name and a default value.
    fn new_zero_value(ctx: &mut ProgramContext, name: &str) -> Self {
        return AConst {
            name: name.to_string(),
            declared_type_key: None,
            value: AExpr::new_zero_value(ctx, Type::new_unresolved("<unknown>")),
        };
    }
}
