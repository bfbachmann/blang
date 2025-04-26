use crate::analyzer::ast::expr::AExpr;
use crate::analyzer::type_store::TypeKey;
use crate::lexer::pos::Span;
use crate::parser::ast::func::Function;
use crate::parser::ast::r#const::Const;
use crate::parser::ast::r#enum::EnumType;
use crate::parser::ast::r#extern::ExternFn;
use crate::parser::ast::r#struct::StructType;
use crate::parser::ast::spec::SpecType;
use crate::parser::ModID;

#[derive(Debug)]
pub struct ModAlias {
    pub name: String,
    pub target_mod_id: ModID,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum IdentKind {
    Variable {
        is_mut: bool,
        type_key: TypeKey,
    },
    Type {
        is_pub: bool,
        type_key: TypeKey,
        mod_id: Option<ModID>,
    },
    Fn {
        is_pub: bool,
        type_key: TypeKey,
        mod_id: Option<ModID>,
    },
    ExternFn {
        is_pub: bool,
        type_key: TypeKey,
        mod_id: Option<ModID>,
    },
    Const {
        is_pub: bool,
        value: AExpr,
        mod_id: Option<ModID>,
    },

    UncheckedConst(Const),
    UncheckedFn(Function),
    UncheckedExternFn(ExternFn),
    UncheckedStructType(StructType),
    UncheckedEnumType(EnumType),
    UncheckedSpecType(SpecType),
}

impl IdentKind {
    pub fn as_unchecked_fn(&self) -> &Function {
        match self {
            IdentKind::UncheckedFn(func) => func,
            _ => panic!("unexpected ident kind {self:?}"),
        }
    }

    pub fn as_unchecked_extern_fn(&self) -> &ExternFn {
        match self {
            IdentKind::UncheckedExternFn(func) => func,
            _ => panic!("unexpected ident kind {self:?}"),
        }
    }

    pub fn as_unchecked_const(&self) -> &Const {
        match self {
            IdentKind::UncheckedConst(c) => c,
            _ => panic!("unexpected ident kind {self:?}"),
        }
    }

    pub fn as_unchecked_struct_type(&self) -> &StructType {
        match self {
            IdentKind::UncheckedStructType(s) => s,
            _ => panic!("unexpected ident kind {self:?}"),
        }
    }

    pub fn as_unchecked_enum_type(&self) -> &EnumType {
        match self {
            IdentKind::UncheckedEnumType(e) => e,
            _ => panic!("unexpected ident kind {self:?}"),
        }
    }

    pub fn as_unchecked_spec_type(&self) -> &SpecType {
        match self {
            IdentKind::UncheckedSpecType(s) => s,
            _ => panic!("unexpected ident kind {self:?}"),
        }
    }

    pub fn is_unchecked(&self) -> bool {
        match self {
            IdentKind::Variable { .. }
            | IdentKind::Type { .. }
            | IdentKind::Fn { .. }
            | IdentKind::ExternFn { .. }
            | IdentKind::Const { .. } => false,

            IdentKind::UncheckedConst(_)
            | IdentKind::UncheckedFn(_)
            | IdentKind::UncheckedExternFn(_)
            | IdentKind::UncheckedStructType(_)
            | IdentKind::UncheckedEnumType(_)
            | IdentKind::UncheckedSpecType(_) => true,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Ident {
    pub name: String,
    pub kind: IdentKind,
    pub span: Span,
}
