use std::collections::HashMap;
use std::path::PathBuf;

use crate::analyzer::ast::module::AModule;
use crate::analyzer::error::{err_import_cycle, AnalyzeError, ErrorKind};
use crate::analyzer::ident::{Ident, IdentKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::type_store::TypeKey;
use crate::analyzer::warn::AnalyzeWarning;
use crate::codegen::program::CodeGenConfig;
use crate::lexer::pos::{Position, Span};
use crate::parser::{ModID, SrcInfo};
use flamer::flame;

/// An analyzed source file along with any errors or warnings that occurred during its analysis.
#[derive(Debug)]
pub struct AnalyzedModule {
    pub module: AModule,
    pub errors: Vec<AnalyzeError>,
    pub warnings: Vec<AnalyzeWarning>,
}

impl AnalyzedModule {
    /// Creates a new analyzed module.
    pub fn new(
        module: AModule,
        errors: HashMap<Position, AnalyzeError>,
        warns: HashMap<Position, AnalyzeWarning>,
    ) -> AnalyzedModule {
        // Extract and sort errors and warnings by their location in the source file.
        let mut errors: Vec<(Position, AnalyzeError)> =
            errors.into_iter().collect();
        errors.sort_by(|(pos1, _), (pos2, _)| pos1.cmp(pos2));

        let mut warnings: Vec<(Position, AnalyzeWarning)> =
            warns.into_iter().collect();
        warnings.sort_by(|(pos1, _), (pos2, _)| pos1.cmp(pos2));

        AnalyzedModule {
            module,
            errors: errors.into_iter().map(|(_, e)| e).collect(),
            warnings: warnings.into_iter().map(|(_, w)| w.clone()).collect(),
        }
    }
}

/// The result of analysis on a set of source files.
pub struct ProgramAnalysis {
    pub ctx: ProgramContext,
    pub analyzed_mods: HashMap<ModID, AnalyzedModule>,
    pub root_mod_id: ModID,
    pub maybe_main_fn_tk: Option<TypeKey>,
}

/// Analyzes all the given modules.
#[flame]
pub fn analyze_modules(
    src_info: &SrcInfo,
    root_mod_path: &str,
    config: CodeGenConfig,
) -> ProgramAnalysis {
    let mut analyzed_mods: HashMap<ModID, AnalyzedModule> = HashMap::new();
    let root_mod_id = src_info.mod_info.get_id_by_path(root_mod_path).unwrap();
    let builtins_mod_id = src_info.mod_info.get_id_by_path("std/builtins").unwrap();
    let mut ctx = ProgramContext::new(builtins_mod_id, root_mod_id, config);

    // Analyze builtins, then analyze depth-first (bottom-up) from the root module.
    analyze_module(
        &mut ctx,
        &mut analyzed_mods,
        &vec![],
        src_info,
        builtins_mod_id,
    );
    analyze_module(&mut ctx, &mut analyzed_mods, &vec![], src_info, root_mod_id);

    // Try to find and validate the main function in the root module.
    let maybe_main_fn_tk = if let Some(Ident {
        kind: IdentKind::Fn { type_key, .. },
        span,
        ..
    }) = ctx.get_local_ident("main", None)
    {
        let span = *span;
        let type_key = *type_key;
        let root_mod = analyzed_mods.get_mut(&root_mod_id).unwrap();
        check_main_fn(&mut ctx, root_mod, type_key, span);

        Some(type_key)
    } else {
        None
    };

    ProgramAnalysis {
        ctx,
        analyzed_mods,
        root_mod_id,
        maybe_main_fn_tk,
    }
}

/// Recursively analyzes modules bottom-up by following imports.
pub fn analyze_module(
    ctx: &mut ProgramContext,
    analyzed_mods: &mut HashMap<ModID, AnalyzedModule>,
    mod_chain: &Vec<PathBuf>,
    src_info: &SrcInfo,
    mod_id: ModID,
) -> bool {
    // Append the module we're analyzing to the dependency chain.
    let mut new_mod_chain = mod_chain.clone();
    let mod_info = src_info.mod_info.get_by_id(mod_id);
    let mod_path = PathBuf::from(&mod_info.path);
    new_mod_chain.push(mod_path.clone());

    // Make sure all modules that this module depends on are analyzed first.
    for used_mod in src_info.get_used_mods(mod_id) {
        let used_mod_id = match src_info.mod_info.get_id_by_path(&used_mod.path.raw) {
            Some(id) => id,
            None => {
                // Skip missing modules.
                continue;
            }
        };
        let used_mod_info = src_info.mod_info.get_by_id(used_mod_id);
        let used_mod_path = PathBuf::from(&used_mod_info.path);

        // Record error and abort early if there is a cyclical import.
        if new_mod_chain.contains(&used_mod_path) {
            let mut cycle = new_mod_chain.clone();
            cycle.push(used_mod_path);

            let err = err_import_cycle(used_mod, &cycle);
            analyzed_mods.insert(
                mod_id,
                AnalyzedModule::new(
                    AModule::new_empty(),
                    HashMap::from([(err.span.start_pos, err)]),
                    HashMap::new(),
                ),
            );
            return false;
        }

        // Analyze the module only if we have not already done so. If it returns false it means
        // analysis should be aborted because of an import cycle.
        if !analyzed_mods.contains_key(&used_mod_id)
            && !analyze_module(ctx, analyzed_mods, &new_mod_chain, src_info, used_mod_id)
        {
            analyzed_mods.insert(
                mod_id,
                AnalyzedModule::new(
                    AModule::new_empty(),
                    std::mem::take(&mut ctx.errors),
                    std::mem::take(&mut ctx.warnings),
                ),
            );
            return false;
        }
    }

    let analyzed_module = AModule::from(ctx, mod_id, src_info);

    analyzed_mods.insert(
        mod_id,
        AnalyzedModule::new(
            analyzed_module,
            std::mem::take(&mut ctx.errors),
            std::mem::take(&mut ctx.warnings),
        ),
    );
    true
}

/// Checks that given `main` function is declared correctly.
fn check_main_fn(
    ctx: &mut ProgramContext,
    analyzed_module: &mut AnalyzedModule,
    type_key: TypeKey,
    span: Span,
) {
    let sig = ctx.get_type(type_key).to_fn_sig();

    if let Some(params) = &sig.params {
        let span = params.span;
        analyzed_module.errors.push(AnalyzeError::new(
            ErrorKind::InvalidMain,
            format_code!("function {} cannot have parameters", "main").as_str(),
            span,
        ));
    } else if !sig.args.is_empty() {
        let span = sig.args.first().unwrap().span;
        analyzed_module.errors.push(AnalyzeError::new(
            ErrorKind::InvalidMain,
            format_code!("function {} cannot take arguments", "main").as_str(),
            span,
        ));
    } else if sig.maybe_ret_type_key.is_some() {
        analyzed_module.errors.push(AnalyzeError::new(
            ErrorKind::InvalidMain,
            format_code!("function {} cannot have a return type", "main").as_str(),
            span,
        ));
    }
}
