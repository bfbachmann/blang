use std::fmt;
use std::fmt::{Display, Formatter};

use colored::Colorize;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::prog_context::{ProgramContext, ScopedSymbol};
use crate::analyzer::r#type::{RichType, TypeId};
use crate::parser::r#const::Const;
use crate::parser::r#type::Type;
use crate::{format_code, util};

/// Represents a semantically valid constant declaration.
#[derive(Debug, Clone)]
pub struct RichConst {
    pub name: String,
    pub declared_type_id: Option<TypeId>,
    pub value: RichExpr,
}

impl PartialEq for RichConst {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && util::opts_eq(&self.declared_type_id, &other.declared_type_id)
            && self.value == other.value
    }
}

impl Display for RichConst {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.name)?;

        if let Some(typ) = &self.declared_type_id {
            write!(f, ": {}", typ)?;
        }

        write!(f, " = {}", self.value)
    }
}

impl RichConst {
    /// Analyzes a const declaration and returns a semantically valid, type-rich constant
    /// declaration.
    pub fn from(ctx: &mut ProgramContext, const_decl: &Const) -> Self {
        // Make sure this const name doesn't collide with any other const names.
        if ctx.get_symbol(const_decl.name.as_str()).is_some() {
            ctx.add_err(AnalyzeError::new(
                ErrorKind::ConstAlreadyDefined,
                format_code!(
                    "constant {} is already defined in this scope",
                    const_decl.name
                )
                .as_str(),
                const_decl,
            ));

            return RichConst::new_zero_value(ctx, const_decl.name.as_str());
        }

        // Make sure the constant value is a valid constant.
        let value = RichExpr::from(ctx, const_decl.value.clone());
        if !value.kind.is_const() {
            ctx.add_err(
                AnalyzeError::new(
                    ErrorKind::InvalidConst,
                    format_code!("{} is not a constant expression", value).as_str(),
                    const_decl,
                )
                .with_detail("Constant expressions cannot contain variables or function calls."),
            );

            return RichConst::new_zero_value(ctx, const_decl.name.as_str());
        }

        // Analyze the optional constant type.
        let type_id = if let Some(parsed_type) = &const_decl.typ {
            // Make sure the expression type matches the declared constant type.
            let declared_type_id = RichType::analyze(ctx, parsed_type);
            let value_type = ctx.must_get_resolved_type(&value.type_id);

            // Skip the check if the declared type could not be resolved.
            let declared_type = ctx.must_get_resolved_type(&declared_type_id);
            if !declared_type.is_unknown() && value_type != declared_type {
                ctx.add_err(AnalyzeError::new(
                    ErrorKind::MismatchedTypes,
                    format_code!(
                        "constant value {} has type {} that does not have declared type {}",
                        value,
                        value_type,
                        declared_type
                    )
                    .as_str(),
                    const_decl,
                ));

                return RichConst::new_zero_value(ctx, const_decl.name.as_str());
            }

            Some(declared_type_id)
        } else {
            None
        };

        // Add the constant to the program context so it can be used later.
        ctx.add_symbol(ScopedSymbol::new_const(
            const_decl.name.as_str(),
            value.type_id.clone(),
        ));

        RichConst {
            name: const_decl.name.clone(),
            declared_type_id: type_id,
            value,
        }
    }

    /// Creates a new constant with the given name and a default value.
    fn new_zero_value(ctx: &mut ProgramContext, name: &str) -> Self {
        return RichConst {
            name: name.to_string(),
            declared_type_id: None,
            value: RichExpr::new_zero_value(ctx, Type::new_unknown("")),
        };
    }
}
