use std::fmt::{Display, Formatter};

use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::ast::r#type::AType;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::parser::r#type::Type;
use crate::parser::tuple::{TupleInit, TupleType};
use crate::util;

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub struct ATupleType {
    pub type_keys: Vec<TypeKey>,
}

impl Display for ATupleType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;

        for (i, typ) in self.type_keys.iter().enumerate() {
            write!(f, "{}", typ)?;

            if i + 1 < self.type_keys.len() {
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
        let mut type_keys = vec![];
        for typ in &tuple_type.field_types {
            let type_key = ctx.resolve_type(typ);
            type_keys.push(type_key);
        }

        ATupleType { type_keys }
    }

    /// Returns a string containing the human-readable version of this tuple type.
    pub fn display(&self, ctx: &ProgramContext) -> String {
        let mut s = format!("{{");

        for (i, tk) in self.type_keys.iter().enumerate() {
            s += format!("{}", ctx.display_type_for_key(*tk)).as_str();

            if i + 1 < self.type_keys.len() {
                s += format!(", ").as_str();
            }
        }

        s + format!("}}").as_str()
    }
}

#[derive(Debug, Clone)]
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

impl PartialEq for ATupleInit {
    fn eq(&self, other: &Self) -> bool {
        self.type_key == other.type_key && util::vecs_eq(&self.values, &other.values)
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
    pub fn from(ctx: &mut ProgramContext, tuple_init: &TupleInit) -> ATupleInit {
        let mut field_values = vec![];
        let mut field_type_keys = vec![];
        for expr in &tuple_init.values {
            let val = AExpr::from(ctx, expr.clone(), None, false);
            field_type_keys.push(val.type_key);
            field_values.push(val);
        }

        let type_key = ctx.insert_type(AType::Tuple(ATupleType {
            type_keys: field_type_keys,
        }));

        ATupleInit {
            type_key,
            values: field_values,
        }
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
