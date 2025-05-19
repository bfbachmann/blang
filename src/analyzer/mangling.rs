use crate::analyzer::ast::r#type::AType;
use crate::analyzer::prog_context::Monomorphization;
use crate::analyzer::type_store::{GetType, TypeKey};
use crate::lexer::pos::Span;
use crate::parser::ModID;
use base_62;
use std::collections::HashMap;

pub fn mangle_type<T: GetType>(
    t: &T,
    mut type_key: TypeKey,
    type_mappings: &HashMap<TypeKey, TypeKey>,
    type_monomorphizations: &HashMap<TypeKey, Monomorphization>,
) -> String {
    let mut param_tks: Vec<TypeKey> = if let Some(mono) = type_monomorphizations.get(&type_key) {
        type_key = mono.poly_type_key;
        mono.replaced_params
            .iter()
            .map(|rp| {
                *type_mappings
                    .get(&rp.replacement_type_key)
                    .unwrap_or(&rp.replacement_type_key)
            })
            .collect()
    } else {
        vec![]
    };

    let typ = t.get_type(type_key);
    let name = typ.name();

    if name.starts_with("anon_fn::") {
        param_tks = type_mappings.values().cloned().collect();
    } else if param_tks.is_empty() {
        param_tks = match typ.params() {
            Some(params) => params
                .params
                .iter()
                .map(|p| *type_mappings.get(&p.generic_type_key).unwrap())
                .collect(),
            None => {
                vec![]
            }
        }
    };

    let impl_type_prefix = match typ {
        AType::Function(fn_sig) => match &fn_sig.maybe_impl_type_key {
            Some(impl_tk) => {
                if let Some(impl_params) = t.get_type(*impl_tk).params() {
                    for param in &impl_params.params {
                        param_tks.push(*type_mappings.get(&param.generic_type_key).unwrap());
                    }
                } else if let Some(mono) = type_monomorphizations.get(impl_tk) {
                    param_tks.extend(mono.replaced_params.iter().map(|rp| {
                        *type_mappings
                            .get(&rp.replacement_type_key)
                            .unwrap_or(&rp.replacement_type_key)
                    }));
                }

                format!("{}.", t.get_type(*impl_tk).name())
            }

            None => "".to_string(),
        },

        _ => "".to_string(),
    };

    let mangled_name = mangle(
        &format!("{}{}", impl_type_prefix, name),
        &typ.span(),
        param_tks.as_slice(),
    );

    mangled_name
}

pub fn mangle_name(name: &str, mod_id: ModID) -> String {
    format!("_{}_{}", serialize(&vec![mod_id]), name)
}

pub fn mangle(name: &str, span: &Span, param_tks: &[TypeKey]) -> String {
    let mut prefix: Vec<u32> = vec![span.file_id, span.start_pos.line, span.start_pos.col];

    for tk in param_tks {
        prefix.push(*tk);
    }

    format!("_{}_{}", serialize(&prefix), name)
}

fn serialize(values: &Vec<u32>) -> String {
    let mut bytes = Vec::with_capacity(4 * values.len());
    for v in values {
        bytes.extend_from_slice(&v.to_le_bytes());
    }
    base_62::encode(&bytes)
}
