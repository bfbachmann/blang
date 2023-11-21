use std::fmt;
use std::fmt::{Display, Formatter};

use colored::Colorize;

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
        // Make sure this const name doesn't collide with any other const names.
        if ctx.get_symbol(const_decl.name.as_str()).is_some() {
            ctx.insert_err(AnalyzeError::new(
                ErrorKind::DuplicateConst,
                format_code!(
                    "constant {} is already defined in this scope",
                    const_decl.name
                )
                .as_str(),
                const_decl,
            ));

            return AConst::new_zero_value(ctx, const_decl.name.as_str());
        }

        // Analyze the optional constant type.
        let declared_tk = match &const_decl.maybe_type {
            Some(typ) => Some(ctx.resolve_type(typ)),
            None => None,
        };

        // Make sure the constant value is a valid constant.
        let value = AExpr::from(ctx, const_decl.value.clone(), declared_tk, false);
        if !value.kind.is_const() {
            ctx.insert_err(
                AnalyzeError::new(
                    ErrorKind::InvalidConst,
                    format_code!("{} is not a constant expression", value.display(ctx)).as_str(),
                    const_decl,
                )
                .with_detail("Constant expressions cannot contain variables or function calls."),
            );

            return AConst::new_zero_value(ctx, const_decl.name.as_str());
        }

        // Add the constant to the program context so it can be used later.
        ctx.insert_symbol(ScopedSymbol::new_const(
            const_decl.name.as_str(),
            value.type_key,
        ));

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
