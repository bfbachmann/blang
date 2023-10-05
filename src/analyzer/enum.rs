use std::cmp::max;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

use colored::Colorize;

use crate::analyzer::error::{AnalyzeError, AnalyzeResult, ErrorKind};
use crate::analyzer::expr::RichExpr;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::program::check_type_containment;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::fmt::hierarchy_to_string;
use crate::lexer::token_kind::TokenKind;
use crate::parser::r#enum::{EnumType, EnumVariantInit};
use crate::parser::r#type::Type;
use crate::{format_code, util};

/// Represents a semantically valid enum type variant declaration.
#[derive(Debug)]
pub struct RichEnumTypeVariant {
    pub number: usize,
    pub name: String,
    pub maybe_type_id: Option<TypeId>,
}

impl Clone for RichEnumTypeVariant {
    fn clone(&self) -> Self {
        RichEnumTypeVariant {
            number: self.number,
            name: self.name.clone(),
            maybe_type_id: self.maybe_type_id.clone(),
        }
    }
}

impl PartialEq for RichEnumTypeVariant {
    fn eq(&self, other: &Self) -> bool {
        self.number == other.number
            && self.name == other.name
            && util::opts_eq(&self.maybe_type_id, &other.maybe_type_id)
    }
}

impl Display for RichEnumTypeVariant {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;

        if let Some(type_id) = &self.maybe_type_id {
            write!(f, "({})", type_id)?;
        }

        Ok(())
    }
}

/// Represents a semantically valid enum type declaration.
#[derive(Debug)]
pub struct RichEnumType {
    pub name: String,
    pub variants: HashMap<String, RichEnumTypeVariant>,
    pub largest_variant_size_bytes: u32,
}

impl PartialEq for RichEnumType {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && util::hashmaps_eq(&self.variants, &other.variants)
    }
}

impl Clone for RichEnumType {
    fn clone(&self) -> Self {
        RichEnumType {
            name: self.name.clone(),
            variants: self.variants.clone(),
            largest_variant_size_bytes: self.largest_variant_size_bytes,
        }
    }
}

impl Display for RichEnumType {
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

impl RichEnumType {
    /// Performs semantic analysis on an enum type declaration.
    pub fn from(ctx: &mut ProgramContext, enum_type: &EnumType) -> Self {
        // Before analyzing enum variant types, we'll prematurely add this (currently-empty) enum
        // type to the program context. This way, if any of the variant types make use of this enum
        // type, we won't get into an infinitely recursive type resolution cycle. When we're done
        // analyzing this type, the mapping will be updated in the program context.
        let type_id = TypeId::from(Type::new_unknown(enum_type.name.as_str()));
        ctx.add_resolved_type(
            type_id.clone(),
            RichType::Enum(RichEnumType {
                name: enum_type.name.clone(),
                variants: HashMap::new(),
                largest_variant_size_bytes: 0,
            }),
        );

        // Analyze each variant in the enum type.
        let mut largest_variant_size_bytes: u32 = 0;
        let mut variants: HashMap<String, RichEnumTypeVariant> = HashMap::new();
        for (i, variant) in enum_type.variants.iter().enumerate() {
            // Make sure the variant name is unique.
            if variants.contains_key(&variant.name) {
                ctx.add_err(AnalyzeError::new(
                    ErrorKind::DuplicateEnumVariant,
                    format_code!(
                        "enum type {} already has a variant named {}",
                        enum_type.name,
                        variant.name
                    )
                    .as_str(),
                    variant,
                ));

                // Ignore this variant since it's illegal.
                continue;
            }

            // Analyze the variant type, if any.
            let maybe_type_id = match &variant.maybe_type {
                Some(typ) => {
                    let variant_type_id = RichType::analyze(ctx, &typ);

                    // Update the size of the largest variant, if necessary.
                    let variant_type = ctx.get_resolved_type(&variant_type_id).unwrap();
                    largest_variant_size_bytes =
                        max(largest_variant_size_bytes, variant_type.size_bytes(ctx));

                    Some(variant_type_id)
                }
                None => None,
            };

            variants.insert(
                variant.name.clone(),
                RichEnumTypeVariant {
                    number: i,
                    name: variant.name.clone(),
                    maybe_type_id,
                },
            );
        }

        let rich_enum = RichEnumType {
            name: enum_type.name.clone(),
            variants,
            largest_variant_size_bytes,
        };

        // Make sure the enum doesn't contain itself via other types.
        let rich_enum_type = RichType::Enum(rich_enum.clone());
        if let Some(type_hierarchy) = rich_enum_type.contains_type(ctx, &rich_enum_type) {
            ctx.add_err(
                AnalyzeError::new(
                    ErrorKind::InfiniteSizedType,
                    format_code!(
                        "enum {} cannot contain itself via any of its field types",
                        enum_type.name,
                    )
                    .as_str(),
                    enum_type,
                )
                .with_detail(
                    format!(
                        "The offending type hierarchy is {}.",
                        hierarchy_to_string(type_hierarchy.iter().map(|t| t.to_string()).collect())
                    )
                    .as_str(),
                )
                .with_help("Consider using reference types instead."),
            );
        }

        // Now that we have a fully analyzed enum type, we can add it to the program context so it
        // can be referenced later.
        ctx.add_enum(rich_enum.clone());
        ctx.add_resolved_type(type_id, RichType::Enum(rich_enum.clone()));
        rich_enum
    }
}

/// Represents a semantically valid enum variant initialization.
#[derive(Debug)]
pub struct RichEnumVariantInit {
    pub enum_type_id: TypeId,
    pub variant: RichEnumTypeVariant,
    pub maybe_value: Option<Box<RichExpr>>,
}

impl PartialEq for RichEnumVariantInit {
    fn eq(&self, other: &Self) -> bool {
        self.enum_type_id == other.enum_type_id
            && self.variant == other.variant
            && util::opts_eq(&self.maybe_value, &other.maybe_value)
    }
}

impl Display for RichEnumVariantInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}{}",
            self.enum_type_id,
            TokenKind::DoubleColon,
            self.variant.name
        )?;

        if let Some(value) = &self.maybe_value {
            write!(f, "({})", value)?;
        }

        Ok(())
    }
}

impl Clone for RichEnumVariantInit {
    fn clone(&self) -> Self {
        RichEnumVariantInit {
            enum_type_id: self.enum_type_id.clone(),
            variant: self.variant.clone(),
            maybe_value: self.maybe_value.clone(),
        }
    }
}

impl RichEnumVariantInit {
    /// Performs semantic analysis on enum variant initialization.
    pub fn from(ctx: &mut ProgramContext, enum_init: &EnumVariantInit) -> Self {
        // Make sure the enum type exists.
        let enum_type_id = RichType::analyze(ctx, &enum_init.enum_type);
        let enum_type = match ctx.get_resolved_type(&enum_type_id).unwrap() {
            RichType::Enum(enum_type) => enum_type,
            other => {
                // This is not an enum type. Record the error and return a placeholder value.
                ctx.add_err(AnalyzeError::new(
                    ErrorKind::TypeIsNotEnum,
                    format_code!("type {} is not an enum, but is being used like one", other)
                        .as_str(),
                    enum_init,
                ));

                return RichEnumVariantInit {
                    enum_type_id,
                    variant: RichEnumTypeVariant {
                        number: 0,
                        name: "<unknown>".to_string(),
                        maybe_type_id: None,
                    },
                    maybe_value: None,
                };
            }
        };

        // Make sure the enum variant exists.
        let variant = match enum_type.variants.get(&enum_init.variant_name) {
            Some(v) => v.clone(),
            None => {
                // This enum type has no such variant. Record the error and return a placeholder
                // value.
                ctx.add_err(AnalyzeError::new(
                    ErrorKind::TypeIsNotEnum,
                    format_code!("enum {} has no variant", enum_init.variant_name).as_str(),
                    enum_init,
                ));

                return RichEnumVariantInit {
                    enum_type_id,
                    variant: RichEnumTypeVariant {
                        number: 0,
                        name: "<unknown>".to_string(),
                        maybe_type_id: None,
                    },
                    maybe_value: None,
                };
            }
        };

        // Analyze the variant value, if one exists. Then make sure the variant value's type
        // matches that of the variant.
        let maybe_value = match &enum_init.maybe_value {
            Some(value) => {
                if variant.maybe_type_id.is_none() {
                    // A value was not expected but was provided. Record the error and return a
                    // placeholder value.
                    ctx.add_err(AnalyzeError::new(
                        ErrorKind::MismatchedTypes,
                        format_code!(
                            "variant {} of enum {} has no associated type, but a value was provided",
                            variant,
                            enum_type.name,
                        )
                        .as_str(),
                        enum_init,
                    ));

                    return RichEnumVariantInit {
                        enum_type_id,
                        variant,
                        maybe_value: None,
                    };
                }

                Some(Box::new(RichExpr::from(ctx, value.as_ref().clone())))
            }
            None => {
                if let Some(type_id) = &variant.maybe_type_id {
                    // A value was expected but was not provided. Record the error and return a
                    // placeholder value.
                    ctx.add_err(AnalyzeError::new(
                        ErrorKind::MismatchedTypes,
                        format_code!(
                            "missing value of type {} for variant {} of enum {}",
                            type_id,
                            variant,
                            enum_type.name
                        )
                        .as_str(),
                        enum_init,
                    ));

                    return RichEnumVariantInit {
                        enum_type_id,
                        variant,
                        maybe_value: None,
                    };
                }

                None
            }
        };

        RichEnumVariantInit {
            enum_type_id,
            variant,
            maybe_value,
        }
    }
}

/// Analyzes type containment within the given enum type and returns an error if there are any
/// illegal type containment cycles that would result in infinite-sized types.
pub fn check_enum_containment_cycles(
    ctx: &ProgramContext,
    enum_type: &EnumType,
    hierarchy: &mut Vec<String>,
) -> AnalyzeResult<()> {
    if hierarchy.contains(&enum_type.name) {
        return Err(AnalyzeError::new(
            ErrorKind::InfiniteSizedType,
            format_code!("enum type {} cannot contain itself", enum_type.name).as_str(),
            enum_type,
        ));
    }

    // Push this type name onto the hierarchy stack so it can be checked against other types.
    hierarchy.push(enum_type.name.clone());

    // Recursively check each enum variant type.
    for variant in &enum_type.variants {
        if let Some(typ) = &variant.maybe_type {
            check_type_containment(ctx, typ, hierarchy)?;
        }
    }

    // Pop this type name off the hierarchy stack because all types it contains have been
    // checked.
    hierarchy.pop();

    Ok(())
}
