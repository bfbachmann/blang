use std::fmt::{Display, Formatter};

use colored::Colorize;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::{RichType, TypeId};
use crate::lexer::pos::{Locatable, Position};
use crate::parser::member::MemberAccess;
use crate::parser::var::Var;
use crate::{format_code, util};

/// Represents a variable, either by name or by access to one of its members.
#[derive(Debug, Clone)]
pub struct RichVar {
    pub var_name: String,
    /// The type ID of the parent variable (i.e. not the member(s) being accessed).
    pub var_type_id: TypeId,
    pub member_access: Option<RichMemberAccess>,
    start_pos: Position,
    end_pos: Position,
}

impl Locatable for RichVar {
    fn start_pos(&self) -> &Position {
        &self.start_pos
    }

    fn end_pos(&self) -> &Position {
        &self.end_pos
    }
}

impl Display for RichVar {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.var_name)?;

        if let Some(access) = &self.member_access {
            write!(f, ".{}", access)?;
        }

        Ok(())
    }
}

impl PartialEq for RichVar {
    fn eq(&self, other: &Self) -> bool {
        self.var_name == other.var_name
            && self.var_type_id == other.var_type_id
            && util::optionals_are_equal(&self.member_access, &other.member_access)
    }
}

impl RichVar {
    /// Creates a new variable with default start and end positions.
    pub fn new_with_default_pos(
        name: &str,
        type_id: TypeId,
        member_access: Option<RichMemberAccess>,
    ) -> Self {
        RichVar {
            var_name: name.to_string(),
            var_type_id: type_id,
            member_access,
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Attempts to analyze the variable (including member accesses). If `include_fns` is
    /// `true`, functions and extern functions will also be searched for the variable name.
    /// Otherwise, only variables will be searched.
    pub fn from(ctx: &mut ProgramContext, var: &Var, include_fns: bool) -> Self {
        // Find the type ID for the variable or member being accessed.
        // Return a placeholder value if we failed to resolve the variable type ID.
        let maybe_type_id =
            RichVar::get_type_id_by_var_name(ctx, var.var_name.as_str(), include_fns);
        let type_id = match maybe_type_id {
            Some(t) => t,
            None => {
                // We could not find the variable or function with the given name, so record the
                // error and return a placeholder value.
                ctx.add_err(AnalyzeError::new_with_locatable(
                    ErrorKind::VariableNotDefined,
                    format_code!("{} is not defined in this scope", var.var_name).as_str(),
                    Box::new(var.clone()),
                ));

                return RichVar::new_with_default_pos(
                    var.var_name.as_str(),
                    TypeId::unknown(),
                    None,
                );
            }
        };

        // Recursively analyze member accesses, if any.
        let member_access = match &var.member_access {
            Some(access) => Some(RichMemberAccess::from(ctx, &type_id, access)),
            None => None,
        };

        RichVar {
            var_name: var.var_name.clone(),
            var_type_id: type_id,
            member_access,
            start_pos: var.start_pos().clone(),
            end_pos: var.end_pos().clone(),
        }
    }

    /// Returns the type ID of the accessed submember (i.e. the type of the member at the end of
    /// the member access chain), or of the variable itself if there is no member access.
    pub fn get_type_id(&self) -> &TypeId {
        match &self.member_access {
            Some(ma) => ma.get_type_id(),
            None => &self.var_type_id,
        }
    }

    /// Returns the name of the lowest level member on this variable access, or just the variable
    /// name if there is no member access.
    pub fn get_last_member_name(&self) -> String {
        match &self.member_access {
            Some(access) => access.get_last_member_name(),
            None => self.var_name.to_string(),
        }
    }

    /// Attempts to find the type ID of a variable given the variable name.
    fn get_type_id_by_var_name(
        ctx: &ProgramContext,
        name: &str,
        include_fns: bool,
    ) -> Option<TypeId> {
        // Search for a variable with the given name. Variables take precedence over functions.
        match ctx.get_var(name) {
            Some(var) => {
                return Some(var.type_id.clone());
            }
            None => {}
        }

        if include_fns {
            // Search for a function with the given name. Functions take precedence over extern
            // functions.
            match ctx.get_fn(name) {
                Some(func) => return Some(func.signature.type_id.clone()),
                None => {}
            };

            // Search for an extern function with the given name. Extern functions take precedence over
            // types.
            match ctx.get_extern_fn(name) {
                Some(fn_sig) => return Some(fn_sig.type_id.clone()),
                None => None,
            }
        } else {
            None
        }
    }
}

/// Represents a member access on a variable or type.
#[derive(Debug, Clone)]
pub struct RichMemberAccess {
    pub member_name: String,
    pub member_type_id: TypeId,
    pub submember: Option<Box<RichMemberAccess>>,
}

impl Display for RichMemberAccess {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.member_name)?;

        if let Some(access) = &self.submember {
            write!(f, ".{}", access)?;
        }

        Ok(())
    }
}

impl PartialEq for RichMemberAccess {
    fn eq(&self, other: &Self) -> bool {
        self.member_name == other.member_name
            && self.member_type_id == other.member_type_id
            && util::optionals_are_equal(&self.submember, &other.submember)
    }
}

impl RichMemberAccess {
    /// Attempts to recursively analyze a member access on the given type.
    fn from(ctx: &mut ProgramContext, type_id: &TypeId, member_access: &MemberAccess) -> Self {
        let typ = ctx.get_resolved_type(type_id).unwrap();

        // Check if the member access is accessing a field on a struct or tuple type.
        let member_name = &member_access.member_name;
        let maybe_field_type_id = match typ {
            RichType::Struct(struct_type) => struct_type.get_field_type(member_name.as_str()),
            RichType::Tuple(tuple_type) => {
                let field_index = member_name.parse::<usize>().unwrap();
                tuple_type.type_ids.get(field_index)
            }
            _ => None,
        };

        // Error and return a placeholder value if we couldn't locate the member being accessed.
        if maybe_field_type_id.is_none() {
            ctx.add_err(AnalyzeError::new_with_locatable(
                ErrorKind::MemberNotDefined,
                format_code!("type {} has no member {}", typ, member_name).as_str(),
                Box::new(member_access.clone()),
            ));

            return RichMemberAccess {
                member_name: member_name.to_string(),
                member_type_id: TypeId::unknown(),
                submember: None,
            };
        }

        // If a submember is being accessed, continue resolving it recursively. Otherwise,
        // just return the field type.
        let field_type_id = maybe_field_type_id.unwrap().clone();
        match &member_access.submember {
            Some(submember) => {
                let submember_access =
                    RichMemberAccess::from(ctx, &field_type_id, submember.as_ref());
                RichMemberAccess {
                    member_name: member_name.to_string(),
                    member_type_id: field_type_id,
                    submember: Some(Box::new(submember_access)),
                }
            }
            None => RichMemberAccess {
                member_name: member_name.to_string(),
                member_type_id: field_type_id,
                submember: None,
            },
        }
    }

    /// Returns the type ID of the accessed submember (i.e. the type of the member at the end
    /// of the member access chain).
    fn get_type_id(&self) -> &TypeId {
        match &self.submember {
            Some(sub) => sub.get_type_id(),
            None => &self.member_type_id,
        }
    }

    /// Returns the name of the lowest level member on this member access, or just the member
    /// name if there is no sub-member access.
    pub fn get_last_member_name(&self) -> String {
        match &self.submember {
            Some(sub) => sub.get_last_member_name(),
            None => self.member_name.to_string(),
        }
    }
}
