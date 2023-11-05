// use crate::analyzer::error::AnalyzeResult;
// use crate::analyzer::func::RichFn;
// use crate::analyzer::func_sig::RichFnSig;
// use crate::analyzer::prog_context::ProgramContext;
// use crate::analyzer::r#type::{RichType, TypeId};
//
// pub fn render_type(
//     ctx: &mut ProgramContext,
//     typ: RichType,
//     target_type: &RichType,
// ) -> AnalyzeResult<TypeId> {
//     assert!(typ.is_templated());
//
//     match (typ, target_type) {
//         (RichType::Function(sig), RichType::Function(target_sig)) => {
//             render_fn_type(ctx, *sig, target_sig)
//         }
//
//         _ => {
//             todo!()
//         }
//     }
// }
//
// pub fn render_fn_type(
//     ctx: &mut ProgramContext,
//     sig: RichFnSig,
//     target_sig: &RichFnSig,
// ) -> AnalyzeResult<TypeId> {
//     // Un-alias all the aliased types in the function signature.
//     for param in &sig.tmpl_params.unwrap().params {
//         if param.
//     }
// }
