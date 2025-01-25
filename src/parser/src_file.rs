use crate::parser::ast::mod_::ModDecl;
use crate::parser::ast::r#use::UsedModule;
use crate::parser::ast::statement::Statement;
use crate::parser::error::ParseResult;
use crate::parser::{FileID, FileParser};

/// Represents a parsed source file.
#[derive(Debug, PartialEq)]
pub struct SrcFile {
    pub id: FileID,
    pub mod_decl: ModDecl,
    pub used_mods: Vec<UsedModule>,
    pub statements: Vec<Statement>,
}

impl SrcFile {
    /// Attempts to parse a list of statements from the deque of tokens. Expects token sequences of
    /// the form
    ///
    ///     mod <name>
    ///     <statement>
    ///     ...
    ///
    /// where
    ///  - `name` is the module name
    ///  - `statement` is a valid statement
    pub fn parse(parser: &mut FileParser) -> ParseResult<Self> {
        let mod_decl = ModDecl::parse(parser)?;

        let mut statements = vec![];
        let mut used_mods = vec![];

        while parser.tokens.has_next() {
            match Statement::parse(parser) {
                Ok(statement) => match statement {
                    Statement::Use(used_mod) => {
                        used_mods.push(used_mod);
                    }
                    other => statements.push(other),
                },
                Err(err) => return Err(err),
            };
        }

        Ok(SrcFile {
            id: parser.file_id,
            mod_decl,
            used_mods,
            statements,
        })
    }
}
