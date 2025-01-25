use std::collections::HashMap;
use std::path::PathBuf;

use crate::analyzer::ast::module::AModule;
use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::warn::AnalyzeWarning;
use crate::codegen::program::CodeGenConfig;
use crate::fmt::hierarchy_to_string;
use crate::lexer::pos::Position;
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
            errors.into_iter().map(|(p, e)| (p, e)).collect();
        errors.sort_by(|(pos1, _), (pos2, _)| pos1.cmp(pos2));

        let mut warnings: Vec<(Position, AnalyzeWarning)> =
            warns.into_iter().map(|(p, e)| (p, e)).collect();
        warnings.sort_by(|(pos1, _), (pos2, _)| pos1.cmp(&pos2));

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
    pub analyzed_modules: Vec<AnalyzedModule>,
    pub maybe_main_fn_mangled_name: Option<String>,
}

/// Analyzes all the given modules.
#[flame]
pub fn analyze_modules(
    src_info: &SrcInfo,
    root_mod_path: &str,
    config: CodeGenConfig,
) -> ProgramAnalysis {
    let mut analyzed_mods: HashMap<ModID, AnalyzedModule> = HashMap::new();
    let mod_paths = src_info
        .mod_ids()
        .into_iter()
        .map(|mod_id| src_info.mod_info.get_by_id(mod_id).path.as_str())
        .collect();
    let mut ctx = ProgramContext::new(root_mod_path, mod_paths, config);

    // Analyze builtins first.
    let builtins_mod_id = src_info.mod_info.get_id_by_path("std/builtins").unwrap();
    analyze_module(
        src_info,
        &mut ctx,
        &mut analyzed_mods,
        &vec![],
        builtins_mod_id,
    );

    let root_mod_id = src_info.mod_info.get_id_by_path(root_mod_path).unwrap();
    analyze_module(src_info, &mut ctx, &mut analyzed_mods, &vec![], root_mod_id);

    // Try to find the name of the main function in the root module.
    let maybe_fn_sig = ctx
        .get_fn_sig_by_mangled_name(
            None,
            ctx.mangle_name(None, None, None, "main", true).as_str(),
        )
        .unwrap();
    let maybe_main_fn_mangled_name = match maybe_fn_sig {
        Some(sig) => Some(sig.mangled_name.clone()),
        None => None,
    };

    ProgramAnalysis {
        ctx,
        analyzed_modules: analyzed_mods.into_values().collect(),
        maybe_main_fn_mangled_name,
    }
}

/// Recursively analyzes modules bottom-up by following imports.
pub fn analyze_module(
    src_info: &SrcInfo,
    ctx: &mut ProgramContext,
    analyzed_mods: &mut HashMap<ModID, AnalyzedModule>,
    mod_chain: &Vec<PathBuf>,
    mod_id: ModID,
) {
    // Append the module we're analyzing to the dependency chain.
    let mut new_mod_chain = mod_chain.clone();
    let mod_info = src_info.mod_info.get_by_id(mod_id);
    let mod_path = PathBuf::from(&mod_info.path);
    new_mod_chain.push(mod_path.clone());

    // Make sure all modules that this module depends on are analyzed first.
    let mut import_cycle_errs = vec![];
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

        // Record error and skip this import if it is cyclical.
        if new_mod_chain.contains(&used_mod_path) {
            let mut cycle = new_mod_chain.clone();
            cycle.push(used_mod_path);

            let import_cycle = hierarchy_to_string(
                &cycle
                    .iter()
                    .map(|p| p.to_str().unwrap().to_string())
                    .collect(),
            );
            import_cycle_errs.push(
                AnalyzeError::new(ErrorKind::ImportCycle, "import cycle", used_mod).with_detail(
                    format!("The offending import cycle is: {}", import_cycle).as_str(),
                ),
            );

            continue;
        }

        // Analyze the module only if we have not already done so.
        if !analyzed_mods.contains_key(&used_mod_id) {
            analyze_module(src_info, ctx, analyzed_mods, &new_mod_chain, used_mod_id);
        }
    }

    let src_files = src_info.get_src_files(mod_id);
    let analyzed_module = AModule::from(ctx, mod_info.path.clone(), src_files);

    // Append the import cycle errors to the module analysis errors.
    let mut errs = std::mem::take(&mut ctx.errors);
    for cycle_err in import_cycle_errs {
        errs.insert(cycle_err.span.start_pos, cycle_err);
    }

    analyzed_mods.insert(
        mod_id,
        AnalyzedModule::new(analyzed_module, errs, std::mem::take(&mut ctx.warnings)),
    );
}
