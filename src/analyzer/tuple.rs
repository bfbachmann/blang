use std::fmt::{Display, Formatter};

use crate::analyzer::expr::RichExpr;
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::parser::r#type::Type;
use crate::parser::tuple::{TupleInit, TupleType};
use crate::util;

#[derive(Debug)]
pub struct RichTupleType {
    pub type_ids: Vec<TypeId>,
}

impl Clone for RichTupleType {
    fn clone(&self) -> Self {
        RichTupleType {
            type_ids: self.type_ids.iter().map(|t| t.clone()).collect(),
        }
    }
}

impl PartialEq for RichTupleType {
    fn eq(&self, other: &Self) -> bool {
        util::vectors_are_equal(&self.type_ids, &other.type_ids)
    }
}

impl Display for RichTupleType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;

        for (i, typ) in self.type_ids.iter().enumerate() {
            write!(f, "{}", typ)?;

            if i + 1 < self.type_ids.len() {
                write!(f, ", ")?;
            }
        }

        write!(f, "}}")?;

        Ok(())
    }
}

impl RichTupleType {
    pub fn from(ctx: &mut ProgramContext, tuple_type: &TupleType) -> Self {
        let mut type_ids = vec![];
        for typ in &tuple_type.types {
            let type_id = RichType::analyze(ctx, typ);
            type_ids.push(type_id);
        }

        RichTupleType { type_ids }
    }
}

#[derive(Debug, Clone)]
pub struct RichTupleInit {
    pub type_id: TypeId,
    pub values: Vec<RichExpr>,
}

impl Display for RichTupleInit {
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

impl PartialEq for RichTupleInit {
    fn eq(&self, other: &Self) -> bool {
        self.type_id == other.type_id && util::vectors_are_equal(&self.values, &other.values)
    }
}

impl RichTupleInit {
    pub fn new_empty(ctx: &mut ProgramContext) -> Self {
        RichTupleInit {
            type_id: RichType::analyze(ctx, &Type::Tuple(TupleType::new(vec![]))),
            values: vec![],
        }
    }

    pub fn from(ctx: &mut ProgramContext, tuple_init: &TupleInit) -> Self {
        let mut values = vec![];
        let mut types = vec![];
        for expr in &tuple_init.values {
            let val = RichExpr::from(ctx, expr.clone());
            types.push(val.type_id.typ().clone());
            values.push(val);
        }

        RichTupleInit {
            type_id: RichType::analyze(ctx, &Type::Tuple(TupleType::new(types))),
            values,
        }
    }
}