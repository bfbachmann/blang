use std::collections::HashSet;
use std::fmt::{Display, Formatter};

use colored::*;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::{Locatable, Position};
use crate::parser::ast::r#type::Type;
use crate::parser::ast::tmpl_params::{TmplParam, TmplParams};
use crate::parser::ast::unresolved::UnresolvedType;
use crate::{format_code, locatable_impl, util};

/// Represents a template parameter. A template parameter has a name and has either one associated
/// type, a set of associated specs, or no associated type or specs (i.e. is a wildcard parameter).
/// If a template parameter has an associated type, only values of that type can be used in places
/// where the template parameter is used.
/// If a template parameter has an associated set of specs, only values of types that implement
/// all of those specs can be used where the template parameter is used.
/// If a template parameter has no type or specs, any value can be used in its place.
#[derive(Debug, Clone, PartialEq)]
pub struct ATmplParam {
    pub name: String,
    pub required_spec_names: Vec<String>,
    pub aliased_type_key: Option<TypeKey>,
    start_pos: Position,
    end_pos: Position,
}

impl Display for ATmplParam {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;

        if let Some(type_key) = &self.aliased_type_key {
            write!(f, " = {}", type_key)?;
        } else if !self.required_spec_names.is_empty() {
            write!(f, ": ")?;
            for (i, name) in self.required_spec_names.iter().enumerate() {
                match i {
                    0 => write!(f, "{}", name)?,
                    _ => write!(f, " + {}", name)?,
                };
            }
        }

        Ok(())
    }
}

locatable_impl!(ATmplParam);

impl ATmplParam {
    /// Performs semantic analysis on a template parameter.
    fn from(ctx: &mut ProgramContext, tmpl_param: &TmplParam) -> Self {
        if let Some(aliased_type) = &tmpl_param.aliased_type {
            let aliased_type_key = Some(ctx.resolve_type(aliased_type));
            return ATmplParam {
                name: tmpl_param.name.clone(),
                required_spec_names: vec![],
                aliased_type_key,
                start_pos: tmpl_param.start_pos().clone(),
                end_pos: tmpl_param.end_pos().clone(),
            };
        }

        let mut required_spec_names = vec![];
        for required_spec in &tmpl_param.required_specs {
            match required_spec {
                Type::Unresolved(UnresolvedType { name, .. }) => {
                    // Make sure the spec exists.
                    if ctx.get_unchecked_spec(name).is_none() {
                        ctx.insert_err(AnalyzeError::new(
                            ErrorKind::UndefSpec,
                            format_code!("spec {} is not defined in this context", name).as_str(),
                            required_spec,
                        ));

                        // Skip the bad spec.
                        continue;
                    }

                    required_spec_names.push(name.clone());
                }

                other => ctx.insert_err(AnalyzeError::new(
                    ErrorKind::MismatchedTypes,
                    format_code!("type {} is not a spec", other).as_str(),
                    required_spec,
                )),
            }
        }

        ATmplParam {
            name: tmpl_param.name.clone(),
            required_spec_names,
            aliased_type_key: None,
            start_pos: tmpl_param.start_pos().clone(),
            end_pos: tmpl_param.end_pos().clone(),
        }
    }
}

/// A list of template parameters.
#[derive(Debug, Clone)]
pub struct ATmplParams {
    pub params: Vec<ATmplParam>,
}

impl PartialEq for ATmplParams {
    fn eq(&self, other: &Self) -> bool {
        util::vecs_eq(&self.params, &other.params)
    }
}

impl ATmplParams {
    /// Performs semantic analysis on a set of template parameters.
    pub fn from(ctx: &mut ProgramContext, tmpl_params: &TmplParams) -> Self {
        let mut params = vec![];
        let mut param_names = HashSet::new();
        for param in &tmpl_params.params {
            // Record an error and skip this param if another param with the same name already
            // exists.
            if param_names.contains(&param.name) {
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::DuplicateTmplParam,
                    format_code!("parameter {} already exists in this template", param.name)
                        .as_str(),
                    param,
                ));

                continue;
            }

            // Analyze the param.
            let a_param = ATmplParam::from(ctx, param);
            param_names.insert(a_param.name.clone());
            params.push(a_param);
        }

        ATmplParams { params }
    }
}
