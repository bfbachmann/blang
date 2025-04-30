use std::collections::HashMap;
use std::fmt::{Display, Formatter};

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::params::AParams;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{
    err_dup_enum_variant, err_dup_ident, err_expected_enum, err_missing_variant_value,
    err_no_such_variant, err_unexpected_variant_value,
};
use crate::analyzer::ident::Ident;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::Span;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::r#enum::{EnumType, EnumVariantInit};
use crate::parser::ast::r#type::Type;
use crate::util;

/// Represents a semantically valid enum type variant declaration.
#[derive(Debug, Clone)]
pub struct AEnumTypeVariant {
    pub number: usize,
    pub name: String,
    pub maybe_type_key: Option<TypeKey>,
}

impl PartialEq for AEnumTypeVariant {
    fn eq(&self, other: &Self) -> bool {
        self.number == other.number
            && self.name == other.name
            && util::opts_eq(&self.maybe_type_key, &other.maybe_type_key)
    }
}

impl Display for AEnumTypeVariant {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;

        if let Some(type_key) = &self.maybe_type_key {
            write!(f, "({})", type_key)?;
        }

        Ok(())
    }
}

impl AEnumTypeVariant {
    /// Returns a string containing the human-readable version of this enum variant.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        let mut s = format!("{}", self.name);

        if let Some(type_key) = &self.maybe_type_key {
            s += format!("({})", ctx.display_type(*type_key)).as_str();
        }

        s
    }
}

/// Represents a semantically valid enum type declaration.
#[derive(Debug, Clone)]
pub struct AEnumType {
    pub name: String,
    pub mangled_name: String,
    pub maybe_params: Option<AParams>,
    pub variants: HashMap<String, AEnumTypeVariant>,
    pub span: Span,
}

impl PartialEq for AEnumType {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.maybe_params == other.maybe_params
            && self.mangled_name == other.mangled_name
            && util::hashmaps_eq(&self.variants, &other.variants)
    }
}

impl Display for AEnumType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} {{", TokenKind::Enum, self.name)?;

        for (i, variant) in self.variants.values().enumerate() {
            match i {
                0 => write!(f, "{}", variant)?,
                _ => write!(f, ", {}", variant)?,
            }
        }

        write!(f, "}}")
    }
}

impl AEnumType {
    /// Performs semantic analysis on an enum type declaration.
    pub fn from(ctx: &mut ProgramContext, enum_type: &EnumType, is_in_fn: bool) -> Self {
        // Before analyzing enum variant types, we'll prematurely add this (currently-empty) enum
        // type to the program context. This way, if any of the variant types make use of this enum
        // type, we won't get into an infinitely recursive type resolution cycle. When we're done
        // analyzing this type, the mapping will be updated in the program context.
        let mangled_name = ctx.mangle_name(None, None, None, enum_type.name.as_str(), is_in_fn);
        let mut a_enum_type = AEnumType {
            name: enum_type.name.clone(),
            mangled_name: mangled_name.clone(),
            maybe_params: None,
            variants: HashMap::new(),
            span: enum_type.span,
        };
        let type_key = ctx.insert_type(AType::Enum(a_enum_type.clone()));

        if let Err(existing) = ctx.insert_ident(Ident::new_type(
            enum_type.name.clone(),
            enum_type.is_pub,
            type_key,
            Some(ctx.cur_mod_id()),
            enum_type.span, // TODO: use name span
        )) {
            err_dup_ident(&enum_type.name, enum_type.span, existing.span);
        }

        // Analyze parameters.
        let maybe_params = match &enum_type.maybe_params {
            Some(params) => {
                let params = AParams::from(ctx, params, type_key);
                ctx.push_params(params.clone());
                Some(params)
            }
            None => None,
        };

        // Update the stored type with the resolved parameters. It's important that we do this
        // before analyzing any fields because the field types may reference this type, in
        // which case it's important that we know what parameters it expects.
        a_enum_type.maybe_params = maybe_params.clone();
        ctx.replace_type(type_key, AType::Enum(a_enum_type.clone()));

        // Analyze each variant in the enum type.
        let mut variants: HashMap<String, AEnumTypeVariant> = HashMap::new();
        for (i, variant) in enum_type.variants.iter().enumerate() {
            // Make sure the variant name is unique.
            if variants.contains_key(&variant.name) {
                let err = err_dup_enum_variant(&enum_type.name, &variant.name, variant.span);
                ctx.insert_err(err);

                // Ignore this variant since it's illegal.
                continue;
            }

            // Analyze the variant type, if any.
            let maybe_type_key = match &variant.maybe_type {
                Some(typ) => {
                    let variant_type_key = ctx.resolve_type(&typ);
                    Some(variant_type_key)
                }
                None => None,
            };

            variants.insert(
                variant.name.clone(),
                AEnumTypeVariant {
                    number: i,
                    name: variant.name.clone(),
                    maybe_type_key,
                },
            );
        }

        // Update the type in the type store now that we've analyzed its fields.
        let a_enum_type = AEnumType {
            name: enum_type.name.clone(),
            mangled_name,
            maybe_params,
            variants,
            span: enum_type.span,
        };
        ctx.replace_type(type_key, AType::Enum(a_enum_type.clone()));

        if a_enum_type.maybe_params.is_some() {
            // We've analyzed all the variants on this enum, but it's possible that some of the
            // variants had types that were monomorphizations of this enum type. For example, in
            // this enum
            //
            //      enum Thing[T] { One(*Thing[int]) }
            //
            // variant `One` type `*Thing[int]` references a monomorphization of the `Thing` type.
            // If this happens, the monomorphization would actually not be correct at this point
            // because it happened before any of the variants on this type had been analyzed and
            // written back to the type store. In other words, the monomorphization would have
            // happened on an empty type, so we need to redo it on the analyzed type.
            if let Some(monos) = ctx.monomorphized_types.remove(&type_key) {
                for mono in monos {
                    ctx.reexecute_monomorphization(mono);
                }
            }

            // Pop generic parameters now that we're done analyzing the type.
            ctx.pop_params(true);
        }

        a_enum_type
    }
}

/// Represents a semantically valid enum variant initialization.
#[derive(Debug, Clone, PartialEq)]
pub struct AEnumVariantInit {
    pub type_key: TypeKey,
    pub variant: AEnumTypeVariant,
    pub maybe_value: Option<Box<AExpr>>,
    pub span: Span,
}

impl Display for AEnumVariantInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}{}",
            self.type_key,
            TokenKind::DoubleColon,
            self.variant.name
        )?;

        if let Some(value) = &self.maybe_value {
            write!(f, "({})", value)?;
        }

        Ok(())
    }
}

impl AEnumVariantInit {
    /// Performs semantic analysis on enum variant initialization.
    pub fn from(ctx: &mut ProgramContext, enum_init: &EnumVariantInit) -> Self {
        // Make sure the enum type exists.
        let enum_type_key = ctx.resolve_type(&Type::Unresolved(enum_init.typ.clone()));
        let enum_type = match ctx.get_type(enum_type_key) {
            AType::Unknown(_) => {
                // The enum type has already failed semantic analysis, so we should avoid
                // analyzing its initialization and just return some zero-value placeholder instead.
                return AEnumVariantInit {
                    type_key: enum_type_key,
                    variant: AEnumTypeVariant {
                        number: 0,
                        name: "".to_string(),
                        maybe_type_key: None,
                    },
                    maybe_value: None,
                    span: enum_init.span,
                };
            }

            AType::Enum(enum_type) => enum_type,

            _ => {
                // This is not an enum type. Record the error and return a placeholder value.
                let err = err_expected_enum(ctx, enum_type_key, enum_init.span);
                ctx.insert_err(err);

                return AEnumVariantInit {
                    type_key: enum_type_key,
                    variant: AEnumTypeVariant {
                        number: 0,
                        name: "<unknown>".to_string(),
                        maybe_type_key: None,
                    },
                    maybe_value: None,
                    span: enum_init.span,
                };
            }
        };

        // Make sure the enum variant exists.
        let variant = match enum_type.variants.get(&enum_init.variant_name) {
            Some(v) => v.clone(),
            None => {
                // This enum type has no such variant. Record the error and return a placeholder
                // value.
                let err = err_no_such_variant(
                    ctx,
                    enum_type_key,
                    &enum_init.variant_name,
                    enum_init.span,
                );
                ctx.insert_err(err);

                return AEnumVariantInit {
                    type_key: enum_type_key,
                    variant: AEnumTypeVariant {
                        number: 0,
                        name: "<unknown>".to_string(),
                        maybe_type_key: None,
                    },
                    maybe_value: None,
                    span: enum_init.span,
                };
            }
        };

        // Analyze the variant value, if one exists. Then make sure the variant value's type
        // matches that of the variant.
        let maybe_value = match &enum_init.maybe_value {
            Some(value) => {
                if variant.maybe_type_key.is_none() {
                    // A value was not expected but was provided. Record the error and return a
                    // placeholder value.
                    let err = err_unexpected_variant_value(
                        ctx,
                        &variant,
                        &enum_type.name,
                        enum_init.span,
                    );
                    ctx.insert_err(err);

                    return AEnumVariantInit {
                        type_key: enum_type_key,
                        variant,
                        maybe_value: None,
                        span: enum_init.span,
                    };
                }

                Some(Box::new(AExpr::from(
                    ctx,
                    value.as_ref().clone(),
                    variant.maybe_type_key,
                    false,
                    false,
                )))
            }
            None => {
                if let Some(type_key) = &variant.maybe_type_key {
                    // A value was expected but was not provided. Record the error and return a
                    // placeholder value.
                    let err = err_missing_variant_value(
                        ctx,
                        &variant,
                        *type_key,
                        &enum_type.name,
                        enum_init.span,
                    );
                    ctx.insert_err(err);

                    return AEnumVariantInit {
                        type_key: enum_type_key,
                        variant,
                        maybe_value: None,
                        span: enum_init.span,
                    };
                }

                None
            }
        };

        AEnumVariantInit {
            type_key: enum_type_key,
            variant,
            maybe_value,
            span: enum_init.span,
        }
    }

    /// Returns the human-readable version of this enum variant initialization.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        let mut s = format!(
            "{}{}{}",
            ctx.display_type(self.type_key),
            TokenKind::DoubleColon,
            self.variant.name
        );

        if let Some(value) = &self.maybe_value {
            s += format!("({})", value.display(ctx)).as_str();
        }

        s
    }
}
