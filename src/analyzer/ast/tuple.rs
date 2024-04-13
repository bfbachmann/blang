use std::fmt::{Display, Formatter};

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::r#struct::AField;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::parser::ast::r#type::Type;
use crate::parser::ast::tuple::{TupleInit, TupleType};

/// Represents an analyzed tuple type. Tuples are essentially the same as structs, only tuple types
/// cannot be named like struct types, and tuple fields are accessed by field index.
#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub struct ATupleType {
    pub fields: Vec<AField>,
}

impl Display for ATupleType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;

        for (i, field) in self.fields.iter().enumerate() {
            write!(f, "{}", field)?;

            if i + 1 < self.fields.len() {
                write!(f, ", ")?;
            }
        }

        write!(f, "}}")?;

        Ok(())
    }
}

impl ATupleType {
    /// Performs semantic analysis on a tuple type declaration.
    pub fn from(ctx: &mut ProgramContext, tuple_type: &TupleType) -> Self {
        // Analyze tuple fields.
        let mut fields = vec![];
        for (field_index, field_type) in tuple_type.field_types.iter().enumerate() {
            fields.push(AField {
                name: field_index.to_string(),
                type_key: ctx.resolve_type(field_type),
            })
        }

        // Sort fields in order of decreasing size to save memory by reducing the need for padding.
        fields.sort_by(|f1, f2| {
            let type1 = ctx.must_get_type(f1.type_key);
            let type2 = ctx.must_get_type(f2.type_key);
            type2
                .min_size_bytes(&ctx.type_store)
                .cmp(&type1.min_size_bytes(&ctx.type_store))
        });

        ATupleType { fields }
    }

    /// Returns the type key of the field at the given index.
    pub fn get_field_type_key(&self, index: usize) -> Option<TypeKey> {
        for field in &self.fields {
            if field.name == index.to_string() {
                return Some(field.type_key);
            }
        }

        None
    }

    /// Returns the index of the field with the given name. Note that the name in this case will
    /// always actually be a positive integer because tuple fields are accessed by index. The trick
    /// here is that tuple fields are reordered to save memory, but the user will still refer to
    /// them by index in the order that they specified the tuple type in their program.
    pub fn get_field_index(&self, name: &str) -> usize {
        for (i, field) in self.fields.iter().enumerate() {
            if field.name == name.to_string() {
                return i;
            }
        }

        panic!("tuple type {} has no field {}", self, name)
    }

    /// Returns a string containing the human-readable version of this tuple type.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        let mut s = format!("{{");

        for (i, field) in self.fields.iter().enumerate() {
            s += format!("{}", ctx.display_type_for_key(field.type_key)).as_str();

            if i + 1 < self.fields.len() {
                s += format!(", ").as_str();
            }
        }

        s + format!("}}").as_str()
    }

    /// Returns true if this tuple type is the same as `other`. Tuple types are considered the same
    /// if they contain types that are considered the same in the same order.
    pub fn is_same_as(&self, ctx: &ProgramContext, other: &ATupleType) -> bool {
        if self.fields.len() != other.fields.len() {
            return false;
        }

        for (field1, field2) in self.fields.iter().zip(other.fields.iter()) {
            let type1 = ctx.must_get_type(field1.type_key);
            let type2 = ctx.must_get_type(field2.type_key);

            if !type1.is_same_as(ctx, type2, false) {
                return false;
            }
        }

        true
    }
}

/// Tuple initialization.
#[derive(Debug, PartialEq, Clone)]
pub struct ATupleInit {
    pub type_key: TypeKey,
    pub values: Vec<AExpr>,
}

impl Display for ATupleInit {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;

        for (i, typ) in self.values.iter().enumerate() {
            write!(f, "{}", typ)?;

            if i + 1 < self.values.len() {
                write!(f, ", ")?;
            }
        }

        write!(f, "}}")?;

        Ok(())
    }
}

impl ATupleInit {
    /// Creates a new empty tuple.
    pub fn new_empty(ctx: &mut ProgramContext) -> ATupleInit {
        ATupleInit {
            type_key: ctx.resolve_type(&Type::Tuple(TupleType::new_with_default_pos(vec![]))),
            values: vec![],
        }
    }

    /// Performs semantic analysis on a tuple initialization.
    pub fn from(
        ctx: &mut ProgramContext,
        tuple_init: &TupleInit,
        maybe_expected_field_type_keys: Option<Vec<TypeKey>>,
    ) -> ATupleInit {
        let mut field_values: Vec<(AField, AExpr)> = vec![];

        for (i, expr) in tuple_init.values.iter().enumerate() {
            let maybe_expected_field_type = match &maybe_expected_field_type_keys {
                Some(tks) => tks.get(i).copied(),
                None => None,
            };

            let val = AExpr::from(
                ctx,
                expr.clone(),
                maybe_expected_field_type,
                false,
                false,
                false,
            );
            field_values.push((
                AField {
                    name: i.to_string(),
                    type_key: val.type_key,
                },
                val,
            ));
        }

        // Sort fields in order of decreasing size to save memory by reducing the need for padding.
        field_values.sort_by(|f1, f2| {
            let type1 = ctx.must_get_type(f1.0.type_key);
            let type2 = ctx.must_get_type(f2.0.type_key);
            type2
                .min_size_bytes(&ctx.type_store)
                .cmp(&type1.min_size_bytes(&ctx.type_store))
        });

        let mut fields = vec![];
        let mut values = vec![];
        for (field, value) in field_values {
            fields.push(field);
            values.push(value);
        }

        let type_key = ctx.insert_type(AType::Tuple(ATupleType { fields }));

        ATupleInit { type_key, values }
    }

    /// Returns the human-readable version of this tuple initialization.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        let mut s = format!("{{");

        for (i, expr) in self.values.iter().enumerate() {
            s += expr.display(ctx).as_str();

            if i + 1 < self.values.len() {
                s += format!(", ").as_str();
            }
        }

        s + format!("}}").as_str()
    }
}
