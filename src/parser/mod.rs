//! The Blang parser attempts to assemble an AST from the sequence of tokens that the lexer
//! produces.

use crate::lexer::error::LexResult;
use crate::lexer::lex::lex;
use crate::lexer::stream::Stream;
use crate::lexer::token::Token;
use crate::parser::ast::r#use::{ModulePath, UsedModule};
use crate::parser::error::{ErrorKind, ParseError};
use crate::parser::file_parser::FileParser;
use crate::parser::src_file::SrcFile;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Debug;
use std::fs;
use std::path::Path;

pub mod ast;
pub mod error;
pub mod file_parser;
pub mod src_file;
mod tests;

pub type ModID = u32;
pub type FileID = u32;
pub type DirID = u32;

/// Contains info about a module (i.e. a collection of source files under the same namespace).
#[derive(Debug)]
pub struct ModInfo {
    pub path: String,
    pub src_file_ids: HashSet<FileID>,
}

/// Contains info about a source file.
#[derive(Debug)]
pub struct FileInfo {
    pub path: String,
}

/// Contains information about all parsed source files.
#[derive(Default, Debug)]
pub struct FileInfoStore {
    file_info: Vec<FileInfo>,
    file_ids: HashMap<String, FileID>,
}

impl FileInfoStore {
    pub fn get_by_id(&self, id: FileID) -> &FileInfo {
        self.file_info.get(id as usize).unwrap()
    }

    pub fn try_get_file_path_by_id(&self, id: FileID) -> Option<&str> {
        match self.file_info.get(id as usize) {
            Some(file_info) => Some(file_info.path.as_str()),
            None => None,
        }
    }

    fn insert(&mut self, file_info: FileInfo) -> FileID {
        let index = self.file_info.len();
        assert!(self
            .file_ids
            .insert(file_info.path.clone(), index as FileID)
            .is_none());
        self.file_info.push(file_info);
        index as FileID
    }
}

/// Contains information about all parsed modules.
#[derive(Default, Debug)]
pub struct ModInfoStore {
    mod_info: Vec<ModInfo>,
    mod_ids: HashMap<String, ModID>,
}

impl ModInfoStore {
    pub fn is_empty(&self) -> bool {
        self.mod_info.is_empty()
    }

    pub fn insert(&mut self, mod_info: ModInfo) -> ModID {
        let index = self.mod_ids.len();
        assert!(self
            .mod_ids
            .insert(mod_info.path.clone(), index as ModID)
            .is_none());
        self.mod_info.push(mod_info);
        index as ModID
    }

    pub fn get_by_id(&self, id: ModID) -> &ModInfo {
        self.mod_info.get(id as usize).unwrap()
    }

    pub fn get_mut_by_id(&mut self, id: ModID) -> &mut ModInfo {
        self.mod_info.get_mut(id as usize).unwrap()
    }

    pub fn get_id_by_path(&self, mod_path: &str) -> Option<ModID> {
        self.mod_ids.get(mod_path).copied()
    }
}

/// Contains information about a parsed directory of source files.
#[derive(Debug)]
pub struct DirInfo {
    pub path: String,
    pub file_ids: Vec<FileID>,
    pub mod_ids: HashMap<String, ModID>,
}

/// Contains information about all parsed directories.
#[derive(Default, Debug)]
pub struct DirInfoStore {
    dir_info: Vec<DirInfo>,
    dir_ids: HashMap<String, DirID>,
}

impl DirInfoStore {
    fn get_id_by_path(&self, path: &str) -> Option<DirID> {
        self.dir_ids.get(path).copied()
    }

    fn get_mut_by_id(&mut self, id: ModID) -> &mut DirInfo {
        self.dir_info.get_mut(id as usize).unwrap()
    }

    fn get_by_path(&self, path: &str) -> Option<&DirInfo> {
        match self.get_id_by_path(path) {
            Some(id) => self.dir_info.get(id as usize),
            None => None,
        }
    }

    fn insert(&mut self, dir_info: DirInfo) -> DirID {
        let index = self.dir_info.len();
        assert!(self
            .dir_ids
            .insert(dir_info.path.clone(), index as DirID)
            .is_none());
        self.dir_info.push(dir_info);
        index as DirID
    }
}

/// Contains information about all parsed modules, directories, and files in the source tree.
pub struct SrcInfo {
    pub mod_info: ModInfoStore,
    pub file_info: FileInfoStore,
    pub dir_info: DirInfoStore,
    pub src_files: HashMap<FileID, SrcFile>,
}

impl Debug for SrcInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{:#?}", self.mod_info)?;
        writeln!(f, "{:#?}", self.file_info)?;
        writeln!(f, "{:#?}", self.dir_info)
    }
}

impl SrcInfo {
    fn new() -> Self {
        SrcInfo {
            mod_info: Default::default(),
            file_info: Default::default(),
            dir_info: Default::default(),
            src_files: Default::default(),
        }
    }

    #[cfg(test)]
    pub fn new_test_file(file: SrcFile) -> Self {
        SrcInfo::new_test_mods(HashMap::from([("test".to_string(), vec![file])]))
    }

    #[cfg(test)]
    pub fn new_test_mods(src: HashMap<String, Vec<SrcFile>>) -> Self {
        let mut src_info = SrcInfo {
            mod_info: Default::default(),
            file_info: Default::default(),
            dir_info: Default::default(),
            src_files: Default::default(),
        };

        let (_, errs) = parse_mod_dir(
            &mut src_info,
            &ModulePath {
                raw: "std/builtins".to_string(),
                span: Default::default(),
            },
        );
        assert!(errs.is_empty());

        let mut file_id = src_info.file_info.file_ids.len() as FileID;

        for (mod_path, src_files) in src {
            src_info.mod_info.insert(ModInfo {
                path: mod_path,
                src_file_ids: HashSet::from_iter((file_id..).take(src_files.len())),
            });

            for src_file in src_files {
                src_info.src_files.insert(file_id, src_file);
                src_info.file_info.insert(FileInfo {
                    path: format!("test_file_{file_id}.bl"),
                });

                file_id += 1;
            }
        }

        src_info
    }

    pub fn get_src_file(&self, id: FileID) -> &SrcFile {
        self.src_files.get(&id).unwrap()
    }

    pub fn get_src_files(&self, mod_id: ModID) -> Vec<&SrcFile> {
        let mut src_files = vec![];

        let mod_info = self.mod_info.get_by_id(mod_id);
        for file_id in &mod_info.src_file_ids {
            let src_file = self.src_files.get(file_id).unwrap();
            src_files.push(src_file);
        }

        src_files
    }

    /// Returns all modules used by the given module.
    pub fn get_used_mods(&self, mod_id: ModID) -> Vec<&UsedModule> {
        let mut used_mods = vec![];
        let mod_info = self.mod_info.get_by_id(mod_id);

        for file_id in &mod_info.src_file_ids {
            let src_file = self.get_src_file(*file_id);
            used_mods.extend(&src_file.used_mods);
        }

        used_mods
    }
}

/// Parses all modules and their dependencies recursively starting from the given module path.
pub fn parse_mods(mod_path: &str) -> (SrcInfo, Vec<ParseError>) {
    let mut src_info = SrcInfo::new();
    let mut checked_mod_paths = HashSet::new();
    let mut errs = vec![];

    // Start by parsing the builtins and then parse the target module.
    let mut parse_queue = VecDeque::from([
        ModulePath {
            raw: "std/builtins".to_string(),
            span: Default::default(),
        },
        ModulePath {
            raw: mod_path.to_string(),
            span: Default::default(),
        },
    ]);

    while let Some(mod_path) = parse_queue.pop_front() {
        let (mod_ids, parse_errs) = parse_mod_dir(&mut src_info, &mod_path);
        errs.extend(parse_errs);

        for mod_id in mod_ids {
            let mod_info = src_info.mod_info.get_by_id(mod_id);

            for src_file_id in &mod_info.src_file_ids {
                let src_file = src_info.get_src_file(*src_file_id);

                for used_mod_path in &src_file.used_mods {
                    // Only add the module to the parse queue if we haven't already checked it.
                    if checked_mod_paths.insert(used_mod_path.path.raw.clone()) {
                        parse_queue.push_back(used_mod_path.path.clone());
                    }
                }
            }
        }
    }

    (src_info, errs)
}

/// Parses a module directory, updating the given parse info. Returns the IDs of all the modules
/// discovered in the directory, as well as any parse errors that occurred.
pub fn parse_mod_dir(
    parse_info: &mut SrcInfo,
    mod_path: &ModulePath,
) -> (HashSet<ModID>, Vec<ParseError>) {
    let mut errs = vec![];
    let mut discovered_mod_ids = HashSet::new();

    // Find source files in the module directory.
    let dir_id = match locate_module_dir(parse_info, mod_path) {
        Ok(dir_id) => dir_id,
        Err(parse_err) => {
            errs.push(parse_err);
            return (discovered_mod_ids, errs);
        }
    };
    let dir_info = parse_info.dir_info.get_mut_by_id(dir_id);

    for file_id in &dir_info.file_ids {
        let file_info = parse_info.file_info.get_by_id(*file_id);
        let path = &file_info.path;

        // Lex the source file and return early if there are any errors.
        let tokens = match lex_source_file(*file_id, path) {
            Ok(result) => match result {
                Ok(tokens) => tokens,
                Err(err) => {
                    errs.push(ParseError::new(
                        ErrorKind::LexError,
                        &err.message,
                        None,
                        err.span,
                    ));
                    continue;
                }
            },

            Err(err) => {
                errs.push(ParseError::new(
                    ErrorKind::LexError,
                    &err,
                    None,
                    Default::default(),
                ));
                continue;
            }
        };

        // Parse the source file.
        let mut parser = FileParser::new(*file_id, Stream::from(tokens));
        let src_file = match SrcFile::parse(&mut parser) {
            Ok(src_file) => src_file,
            Err(err) => {
                errs.push(err);
                continue;
            }
        };

        // Figure out which module the source file is supposed to belong to.
        let file_mod_name = src_file.mod_decl.name.clone();
        let file_mod_path = if dir_info.path.ends_with(&file_mod_name) {
            dir_info.path.clone()
        } else {
            Path::new(&dir_info.path)
                .join(&file_mod_name)
                .to_str()
                .unwrap()
                .to_string()
        };

        // Find or create the module to which this source file belongs.
        let file_mod_id = match parse_info.mod_info.get_id_by_path(&file_mod_path) {
            Some(id) => id,
            None => parse_info.mod_info.insert(ModInfo {
                path: file_mod_path.clone(),
                src_file_ids: Default::default(),
            }),
        };
        let mod_info = parse_info.mod_info.get_mut_by_id(file_mod_id);

        // Update the file's module with info about the file and the modules it relies on.
        mod_info.src_file_ids.insert(src_file.id);
        parse_info.src_files.insert(*file_id, src_file);
        dir_info.mod_ids.insert(file_mod_name, file_mod_id);

        discovered_mod_ids.insert(file_mod_id);
    }

    (discovered_mod_ids, errs)
}

/// Lexes a source file.
pub fn lex_source_file(file_id: FileID, input_path: &str) -> Result<LexResult<Vec<Token>>, String> {
    let full_path = match fs::canonicalize(input_path) {
        Ok(p) => p,
        Err(err) => return Err(format!("error reading {}: {}", input_path, err)),
    };

    let source_code = match fs::read_to_string(full_path) {
        Ok(code) => code,
        Err(err) => return Err(format!("error reading {}: {}", input_path, err)),
    };

    Ok(lex(source_code.as_str(), file_id))
}

/// Locates the directory that `used_mod` refers to as well as all the source files inside
/// that directory. Adds the directory info to the parse info and returns the directory ID, or an
/// error message.
fn locate_module_dir(ctx: &mut SrcInfo, used_mod_path: &ModulePath) -> Result<DirID, ParseError> {
    // Get the directory path and mod name from the given target mod path.
    let cwd_path = Path::new(".");
    let mod_path = Path::new(&used_mod_path.raw);
    let (dir_path, mod_name) = if mod_path.is_dir() {
        (
            mod_path,
            mod_path
                .components()
                .last()
                .unwrap()
                .as_os_str()
                .to_string_lossy()
                .to_string(),
        )
    } else if mod_path.parent().is_some_and(|parent| parent.is_dir()) {
        (
            mod_path.parent().unwrap(),
            mod_path
                .components()
                .last()
                .unwrap()
                .as_os_str()
                .to_string_lossy()
                .to_string(),
        )
    } else if mod_path.is_file() {
        return Err(ParseError::new(
            ErrorKind::FailedToLocateMod,
            format_code!("module path {} refers to a file", mod_path.display()).as_str(),
            None,
            used_mod_path.span,
        ));
    } else {
        (cwd_path, mod_path.to_string_lossy().to_string())
    };

    // Nothing to do if we've already parsed all the files in this dir.
    let dir_path_str = dir_path.to_str().unwrap();
    if let Some(dir_info) = ctx.dir_info.get_by_path(dir_path_str) {
        return if dir_info.mod_ids.contains_key(&mod_name) {
            let dir_id = ctx.dir_info.get_id_by_path(dir_path_str).unwrap();
            Ok(dir_id)
        } else {
            // If we get here, it means we've already parsed this directory, but the target module
            // does not exist in this directory.
            Err(ParseError::new(
                ErrorKind::FailedToLocateMod,
                format_code!("module {} does not exist in {}", mod_name, dir_path_str).as_str(),
                None,
                used_mod_path.span,
            ))
        };
    }

    let dir = match fs::read_dir(dir_path) {
        Ok(dir) => dir,
        Err(err) => {
            return Err(ParseError::new(
                ErrorKind::FailedToLocateMod,
                format_code!(r#"error reading {}: {}"#, dir_path.display(), err).as_str(),
                None,
                used_mod_path.span,
            ))
        }
    };

    let mut file_ids = vec![];

    for entry in dir {
        match entry {
            Ok(entry) => {
                let path = entry.path();
                if path.extension().is_some_and(|ext| ext == "bl") {
                    let file_id = ctx.file_info.insert(FileInfo {
                        path: path.to_str().unwrap().to_string(),
                    });
                    file_ids.push(file_id);
                }
            }

            Err(err) => {
                return Err(ParseError::new(
                    ErrorKind::FailedToLocateMod,
                    format!(r#"error reading {}: {}"#, dir_path.display(), err).as_str(),
                    None,
                    used_mod_path.span,
                ));
            }
        }
    }

    let dir_id = ctx.dir_info.insert(DirInfo {
        path: match dir_path_str {
            "." => "".to_string(),
            other => other.to_string(),
        },
        file_ids,
        mod_ids: Default::default(),
    });

    Ok(dir_id)
}
