use std::cmp::max;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::fmt::hierarchy_to_string;
use crate::lexer::token_kind::TokenKind;
use crate::parser::ast::r#enum::{EnumType, EnumVariantInit};
use crate::{format_code, util};

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
    /// Converts this variant from a polymorphic (parameterized) type into a
    /// monomorph by substituting type keys for generic types with those from the
    /// provided parameter values.
    pub fn monomorphize(&mut self, type_mappings: &HashMap<TypeKey, TypeKey>) {
        if let Some(tk) = &mut self.maybe_type_key {
            *tk = *type_mappings.get(&tk).unwrap_or(tk);
        }
    }

    /// Returns a string containing the human-readable version of this enum variant.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        let mut s = format!("{}", self.name);

        if let Some(type_key) = &self.maybe_type_key {
            s += format!("({})", ctx.display_type_for_key(*type_key)).as_str();
        }

        s
    }
}

/// Represents a semantically valid enum type declaration.
#[derive(Debug)]
pub struct AEnumType {
    pub name: String,
    pub variants: HashMap<String, AEnumTypeVariant>,
    pub max_variant_size_bytes: u32,
}

impl PartialEq for AEnumType {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && util::hashmaps_eq(&self.variants, &other.variants)
    }
}

impl Clone for AEnumType {
    fn clone(&self) -> Self {
        AEnumType {
            name: self.name.clone(),
            variants: self.variants.clone(),
            max_variant_size_bytes: self.max_variant_size_bytes,
        }
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
    pub fn from(ctx: &mut ProgramContext, enum_type: &EnumType) -> Self {
        // Before analyzing enum variant types, we'll prematurely add this (currently-empty) enum
        // type to the program context. This way, if any of the variant types make use of this enum
        // type, we won't get into an infinitely recursive type resolution cycle. When we're done
        // analyzing this type, the mapping will be updated in the program context.
        let type_key = ctx.insert_type(AType::Enum(AEnumType {
            name: enum_type.name.clone(),
            variants: HashMap::new(),
            max_variant_size_bytes: 0,
        }));

        // Analyze each variant in the enum type.
        let mut largest_variant_size_bytes: u32 = 0;
        let mut variants: HashMap<String, AEnumTypeVariant> = HashMap::new();
        for (i, variant) in enum_type.variants.iter().enumerate() {
            // Make sure the variant name is unique.
            if variants.contains_key(&variant.name) {
                ctx.insert_err(AnalyzeError::new(
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
            let maybe_type_key = match &variant.maybe_type {
                Some(typ) => {
                    let variant_type_key = ctx.resolve_type(&typ);

                    // Update the size of the largest variant, if necessary.
                    let variant_type = ctx.must_get_type(variant_type_key);
                    largest_variant_size_bytes = max(
                        largest_variant_size_bytes,
                        variant_type.min_size_bytes(&ctx.type_store),
                    );

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

        let a_enum = AEnumType {
            name: enum_type.name.clone(),
            variants,
            max_variant_size_bytes: largest_variant_size_bytes,
        };

        // Make sure the enum doesn't contain itself via other types.
        let a_enum_type = AType::Enum(a_enum.clone());
        if let Some(type_hierarchy) = a_enum_type.contains_type(ctx, &a_enum_type) {
            ctx.insert_err(
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
                        hierarchy_to_string(
                            &type_hierarchy.iter().map(|t| t.to_string()).collect()
                        )
                    )
                    .as_str(),
                )
                .with_help("Consider using reference types instead."),
            );
        }

        // Record the type name as public in the current module if necessary.
        if enum_type.is_pub {
            ctx.insert_pub_type_name(enum_type.name.as_str());
        }

        // Now that we have a fully analyzed enum type, we can add it to the program context so it
        // can be referenced later.
        ctx.replace_type(type_key, a_enum_type);

        a_enum
    }

    /// Converts this enum type from a polymorphic (parameterized) type into a
    /// monomorph by substituting type keys for generic types with those from the
    /// provided parameter values.
    pub fn monomorphize(
        &mut self,
        _: &mut ProgramContext,
        type_mappings: &HashMap<TypeKey, TypeKey>,
    ) -> TypeKey {
        for (_, variant) in &mut self.variants {
            variant.monomorphize(type_mappings);
        }

        // TODO: Probably need to insert this new type into the program context
        // here and do something with the type key it returns.
        todo!()
    }

    /// Returns a string containing the human-readable version of this enum type.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        let mut s = format!("{} {} {{", TokenKind::Enum, self.name);

        for (i, variant) in self.variants.values().enumerate() {
            match i {
                0 => s += format!("{}", variant.display(ctx)).as_str(),
                _ => s += format!(", {}", variant.display(ctx)).as_str(),
            }
        }

        s + format!("}}").as_str()
    }
}

/// Represents a semantically valid enum variant initialization.
#[derive(Debug)]
pub struct AEnumVariantInit {
    pub type_key: TypeKey,
    pub variant: AEnumTypeVariant,
    pub maybe_value: Option<Box<AExpr>>,
}

impl PartialEq for AEnumVariantInit {
    fn eq(&self, other: &Self) -> bool {
        self.type_key == other.type_key
            && self.variant == other.variant
            && util::opts_eq(&self.maybe_value, &other.maybe_value)
    }
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

impl Clone for AEnumVariantInit {
    fn clone(&self) -> Self {
        AEnumVariantInit {
            type_key: self.type_key,
            variant: self.variant.clone(),
            maybe_value: self.maybe_value.clone(),
        }
    }
}

impl AEnumVariantInit {
    /// Performs semantic analysis on enum variant initialization.
    pub fn from(ctx: &mut ProgramContext, enum_init: &EnumVariantInit) -> Self {
        // Make sure the enum type exists.
        let enum_type_key = ctx.resolve_type(&enum_init.enum_type);
        let enum_type = match ctx.must_get_type(enum_type_key) {
            AType::Enum(enum_type) => enum_type,
            other => {
                // This is not an enum type. Record the error and return a placeholder value.
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::TypeIsNotEnum,
                    format_code!(
                        "type {} is not an enum, but is being used like one",
                        other.display(ctx)
                    )
                    .as_str(),
                    enum_init,
                ));

                return AEnumVariantInit {
                    type_key: enum_type_key,
                    variant: AEnumTypeVariant {
                        number: 0,
                        name: "<unknown>".to_string(),
                        maybe_type_key: None,
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
                ctx.insert_err(AnalyzeError::new(
                    ErrorKind::TypeIsNotEnum,
                    format_code!("enum {} has no variant", enum_init.variant_name).as_str(),
                    enum_init,
                ));

                return AEnumVariantInit {
                    type_key: enum_type_key,
                    variant: AEnumTypeVariant {
                        number: 0,
                        name: "<unknown>".to_string(),
                        maybe_type_key: None,
                    },
                    maybe_value: None,
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
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::MismatchedTypes,
                        format_code!(
                            "variant {} of enum {} has no associated type, but a value was provided",
                            variant.display(ctx),
                            enum_type.name,
                        )
                            .as_str(),
                        enum_init,
                    ));

                    return AEnumVariantInit {
                        type_key: enum_type_key,
                        variant,
                        maybe_value: None,
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
                    ctx.insert_err(AnalyzeError::new(
                        ErrorKind::MismatchedTypes,
                        format_code!(
                            "missing value of type {} for variant {} of enum {}",
                            ctx.display_type_for_key(*type_key),
                            variant.display(ctx),
                            enum_type.name
                        )
                        .as_str(),
                        enum_init,
                    ));

                    return AEnumVariantInit {
                        type_key: enum_type_key,
                        variant,
                        maybe_value: None,
                    };
                }

                None
            }
        };

        AEnumVariantInit {
            type_key: enum_type_key,
            variant,
            maybe_value,
        }
    }

    /// Returns the human-readable version of this enum variant initialization.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        let mut s = format!(
            "{}{}{}",
            ctx.display_type_for_key(self.type_key),
            TokenKind::DoubleColon,
            self.variant.name
        );

        if let Some(value) = &self.maybe_value {
            s += format!("({})", value.display(ctx)).as_str();
        }

        s
    }
}
