use std::collections::HashMap;
use std::fmt::{Display, Formatter};

use colored::*;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::lexer::pos::{Locatable, Position};
use crate::parser::r#type::Type;
use crate::parser::tmpl_params::{TmplParam, TmplParams};
use crate::parser::unresolved::UnresolvedType;
use crate::{format_code, locatable_impl, util};

/// Represents a template parameter. A template parameter has a name and has either one associated
/// type, a set of associated specs, or no associated type or specs (i.e. is a wildcard parameter).
/// If a template parameter has an associated type, only values of that type can be used in places
/// where the template parameter is used.
/// If a template parameter has an associated set of specs, only values of types that implement
/// all of those specs can be used where the template parameter is used.
/// If a template parameter has no type or specs, any value can be used in its place.
#[derive(Debug, Clone, PartialEq)]
pub struct RichTmplParam {
    pub name: String,
    pub required_spec_names: Vec<String>,
    pub required_type_id: Option<TypeId>,
    start_pos: Position,
    end_pos: Position,
}

impl Display for RichTmplParam {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;

        if let Some(type_id) = &self.required_type_id {
            write!(f, " = {}", type_id)?;
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

locatable_impl!(RichTmplParam);

impl RichTmplParam {
    /// Performs semantic analysis on a template parameter.
    fn from(ctx: &mut ProgramContext, tmpl_param: &TmplParam) -> Self {
        if let Some(required_type) = &tmpl_param.required_type {
            let required_type_id = Some(RichType::analyze(ctx, required_type));
            return RichTmplParam {
                name: tmpl_param.name.clone(),
                required_spec_names: vec![],
                required_type_id,
                start_pos: tmpl_param.start_pos().clone(),
                end_pos: tmpl_param.end_pos().clone(),
            };
        }

        let mut required_spec_names = vec![];
        for required_spec in &tmpl_param.required_specs {
            match required_spec {
                Type::Unresolved(UnresolvedType { name, .. }) => {
                    // Make sure the spec exists.
                    if ctx.get_extern_spec(name).is_none() {
                        ctx.add_err(AnalyzeError::new(
                            ErrorKind::SpecNotDefined,
                            format_code!("spec {} is not defined in this context", name).as_str(),
                            required_spec,
                        ));

                        // Skip the bad spec.
                        continue;
                    }

                    required_spec_names.push(name.clone());
                }

                other => ctx.add_err(AnalyzeError::new(
                    ErrorKind::MismatchedTypes,
                    format_code!("type {} is not a spec", other).as_str(),
                    required_spec,
                )),
            }
        }

        RichTmplParam {
            name: tmpl_param.name.clone(),
            required_spec_names,
            required_type_id: None,
            start_pos: tmpl_param.start_pos().clone(),
            end_pos: tmpl_param.end_pos().clone(),
        }
    }
}

/// A list of template parameters.
#[derive(Debug, Clone)]
pub struct RichTmplParams {
    pub params: HashMap<String, RichTmplParam>,
}

impl PartialEq for RichTmplParams {
    fn eq(&self, other: &Self) -> bool {
        util::hashmaps_eq(&self.params, &other.params)
    }
}

impl RichTmplParams {
    /// Performs semantic analysis on a set of template parameters.
    pub fn from(ctx: &mut ProgramContext, tmpl_params: &TmplParams) -> Self {
        let mut params = HashMap::new();
        for param in &tmpl_params.params {
            // Record an error and skip this param if another param with the same name already
            // exists.
            if params.contains_key(&param.name) {
                ctx.add_err(AnalyzeError::new(
                    ErrorKind::DuplicateTmplParam,
                    format_code!("parameter {} already exists in this template", param.name)
                        .as_str(),
                    param,
                ));

                continue;
            }

            params.insert(param.name.clone(), RichTmplParam::from(ctx, param));
        }

        RichTmplParams { params }
    }
}
