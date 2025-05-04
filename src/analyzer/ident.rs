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
    pub usage: Usage,
    pub span: Span,
}

impl ModAlias {
    pub fn new(name: String, target_mod_id: ModID, span: Span) -> Self {
        Self {
            name,
            target_mod_id,
            usage: Usage::Unused,
            span,
        }
    }
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

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Usage {
    Unused,
    Read,
    Write,
}

#[derive(Debug, Clone)]
pub struct Ident {
    pub name: String,
    pub kind: IdentKind,
    pub usage: Usage,
    pub span: Span,
}

impl Ident {
    pub fn new_type(
        name: String,
        is_pub: bool,
        type_key: TypeKey,
        mod_id: Option<ModID>,
        span: Span,
    ) -> Self {
        Self {
            name,
            kind: IdentKind::Type {
                is_pub,
                type_key,
                mod_id,
            },
            usage: Usage::Unused,
            span,
        }
    }

    pub fn new_var(name: String, is_mut: bool, type_key: TypeKey, span: Span) -> Self {
        Self {
            name,
            kind: IdentKind::Variable { is_mut, type_key },
            usage: Usage::Unused,
            span,
        }
    }

    pub fn new_const(
        name: String,
        is_pub: bool,
        value: AExpr,
        mod_id: Option<ModID>,
        span: Span,
    ) -> Self {
        Self {
            name,
            kind: IdentKind::Const {
                is_pub,
                value,
                mod_id,
            },
            usage: Usage::Unused,
            span,
        }
    }

    pub fn new_fn(func: &Function, type_key: TypeKey, mod_id: Option<ModID>) -> Self {
        Self {
            name: func.signature.name.value.clone(),
            kind: IdentKind::Fn {
                is_pub: func.is_pub,
                type_key,
                mod_id,
            },
            usage: Usage::Unused,
            span: func.signature.name.span,
        }
    }

    pub fn new_extern_fn(
        name: String,
        is_pub: bool,
        type_key: TypeKey,
        mod_id: Option<ModID>,
        span: Span,
    ) -> Self {
        Self {
            name,
            kind: IdentKind::ExternFn {
                is_pub,
                type_key,
                mod_id,
            },
            usage: Usage::Unused,
            span,
        }
    }

    pub fn new_unchecked_struct_type(struct_type: StructType) -> Self {
        Self {
            name: struct_type.name.value.clone(),
            span: struct_type.name.span,
            kind: IdentKind::UncheckedStructType(struct_type),
            usage: Usage::Unused,
        }
    }

    pub fn new_unchecked_enum_type(enum_type: EnumType) -> Self {
        Self {
            name: enum_type.name.value.clone(),
            span: enum_type.name.span,
            kind: IdentKind::UncheckedEnumType(enum_type),
            usage: Usage::Unused,
        }
    }

    pub fn new_unchecked_spec_type(spec_type: SpecType) -> Self {
        Self {
            name: spec_type.name.value.clone(),
            span: spec_type.name.span,
            kind: IdentKind::UncheckedSpecType(spec_type),
            usage: Usage::Unused,
        }
    }

    pub fn new_unchecked_const(const_: Const) -> Self {
        Self {
            name: const_.name.value.clone(),
            span: const_.name.span,
            kind: IdentKind::UncheckedConst(const_),
            usage: Usage::Unused,
        }
    }

    pub fn new_unchecked_fn(func: Function) -> Self {
        Self {
            name: func.signature.name.value.clone(),
            span: func.signature.name.span,
            kind: IdentKind::UncheckedFn(func),
            usage: Usage::Unused,
        }
    }

    pub fn new_unchecked_extern_fn(extern_fn: ExternFn) -> Self {
        Self {
            name: extern_fn.signature.name.value.clone(),
            span: extern_fn.signature.name.span,
            kind: IdentKind::UncheckedExternFn(extern_fn),
            usage: Usage::Unused,
        }
    }

    pub fn is_unused(&self) -> bool {
        matches!(self.usage, Usage::Unused) && self.name != "_"
    }

    pub fn is_unused_top_level(&self) -> bool {
        let is_pub = match &self.kind {
            IdentKind::Variable { .. } => false,
            IdentKind::Type { is_pub, .. } => *is_pub,
            IdentKind::Fn { is_pub, .. } => *is_pub || self.name == "main",
            IdentKind::ExternFn { is_pub, .. } => *is_pub,
            IdentKind::Const { is_pub, .. } => *is_pub,
            IdentKind::UncheckedConst(const_) => const_.is_pub,
            IdentKind::UncheckedFn(func) => func.is_pub,
            IdentKind::UncheckedExternFn(func) => func.is_pub,
            IdentKind::UncheckedStructType(struct_type) => struct_type.is_pub,
            IdentKind::UncheckedEnumType(enum_type) => enum_type.is_pub,
            IdentKind::UncheckedSpecType(spec_type) => spec_type.is_pub,
        };

        self.is_unused() && !is_pub
    }
}
