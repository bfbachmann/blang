use std::collections::{HashMap, HashSet};
use std::default::Default;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

use crate::analyzer::ast::generic::AGenericType;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{err_dup_param, err_expected_spec};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::fmt::vec_to_string;
use crate::lexer::pos::Span;
use crate::locatable_impl;
use crate::parser::ast::params::{Param, Params};
use crate::Locatable;

/// Represents a generic parameter. A generic parameter has a name and has either
/// a set of associated specs, or a constant type, or no associated type or specs
/// (i.e. is a wildcard parameter).
/// If a generic parameter has an associated set of specs, only values of types that implement
/// all of those specs can be used where the generic parameter is used.
/// If a generic parameter has a const type, only constants of that type can
/// be used in its place.
/// If a generic parameter has no type or specs, any value can be used in its place.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AParam {
    pub name: String,
    pub poly_type_key: TypeKey,
    pub generic_type_key: TypeKey,
    pub span: Span,
}

impl Hash for AParam {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.poly_type_key.hash(state);
        self.generic_type_key.hash(state);
    }
}

impl Display for AParam {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.name, self.generic_type_key)
    }
}

locatable_impl!(AParam);

impl AParam {
    /// Performs semantic analysis on a generic parameter.
    /// `poly_type_key` should be the key for the type to which these parameters
    /// apply. It will be used to disambiguate parameters that have the same
    /// name and constraints but apply to different types.
    fn from(ctx: &mut ProgramContext, param: &Param, poly_type_key: TypeKey) -> Self {
        let mut required_spec_type_keys = vec![];
        for required_spec in &param.required_specs {
            // Try resolve the spec type.
            let spec_tk = ctx.resolve_type(&required_spec.as_unresolved_type());
            let spec_type = ctx.get_type(spec_tk);
            match spec_type {
                AType::Spec(_) => {
                    required_spec_type_keys.push(spec_tk);
                }

                AType::Unknown(_) => {}

                _ => {
                    let err = err_expected_spec(ctx, spec_tk, required_spec.span);
                    ctx.insert_err(err);
                }
            }
        }

        // Insert a new generic type with the required spec type keys.
        let generic_type = AGenericType {
            name: param.name.clone(),
            spec_type_keys: HashSet::from_iter(required_spec_type_keys.clone()),
            poly_type_key,
            span: param.span,
        };
        let generic_type_key = ctx.insert_type(AType::Generic(generic_type));

        // Define member functions for the generic type based on its spec constraints.
        // Also mark the generic type as implementing all the specs from its constraints.
        for spec_type_key in required_spec_type_keys {
            let spec = ctx.get_type(spec_type_key).to_spec_type();
            let spec_fn_tks: Vec<TypeKey> = spec.member_fn_type_keys.values().cloned().collect();
            let mut impl_fns = HashMap::new();

            for fn_type_key in spec_fn_tks {
                let mut fn_sig = ctx.get_type(fn_type_key).to_fn_sig().clone();
                fn_sig.replace_type_and_define(ctx, spec_type_key, generic_type_key);
                impl_fns.insert(fn_sig.name, fn_sig.type_key);
            }

            ctx.insert_impl(generic_type_key, Some(spec_type_key), impl_fns);
        }

        AParam {
            name: param.name.clone(),
            generic_type_key,
            poly_type_key,
            span: param.span.clone(),
        }
    }

    /// Returns a string containing this param in human-readable form.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        let mut s = self.name.clone();

        for (i, spec_type_key) in ctx
            .get_type(self.generic_type_key)
            .to_generic_type()
            .spec_type_keys
            .iter()
            .enumerate()
        {
            if i == 0 {
                s += format!(": {}", ctx.display_type(*spec_type_key)).as_str();
            } else {
                s += format!(" + {}", ctx.display_type(*spec_type_key)).as_str();
            }
        }

        s
    }
}

/// A list of compile-time (generic) parameters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AParams {
    pub params: Vec<AParam>,
    pub span: Span,
}

impl Hash for AParams {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.params.hash(state);
    }
}

impl Default for AParams {
    fn default() -> Self {
        AParams {
            params: vec![],
            span: Span::default(),
        }
    }
}

impl Display for AParams {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}]", vec_to_string(&self.params, ","))
    }
}

impl AParams {
    /// Performs semantic analysis on a set of generic parameters.
    /// `poly_type_key` should be the key for the type to which these parameters
    /// apply. It will be used to disambiguate parameters that have the same
    /// name and constraints but apply to different types.
    pub fn from(ctx: &mut ProgramContext, params: &Params, poly_type_key: TypeKey) -> Self {
        let mut a_params: Vec<AParam> = vec![];
        for param in &params.params {
            // Record an error and skip this param if another param with the same name already
            // exists.
            if a_params.iter().find(|p| p.name == param.name).is_some() {
                ctx.insert_err(err_dup_param(&param.name, param.span));
                continue;
            }

            // Analyze the param.
            let a_param = AParam::from(ctx, param, poly_type_key);
            a_params.push(a_param);
        }

        AParams {
            params: a_params,
            span: params.span,
        }
    }

    /// Returns a string containing this set of parameters in human-readable form.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        let mut s = "[".to_string();

        for (i, param) in self.params.iter().enumerate() {
            if i == 0 {
                s += format!("{}", param.display(ctx)).as_str();
            } else {
                s += format!(", {}", param.display(ctx)).as_str();
            }
        }

        s + "]"
    }
}
