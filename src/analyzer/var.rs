use std::fmt::{Display, Formatter};

use colored::Colorize;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::ProgramContext;
use crate::analyzer::r#type::{RichType, TypeId};
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
    /// Creates a new variable.
    #[cfg(test)]
    pub fn new(name: &str, type_id: TypeId, member_access: Option<RichMemberAccess>) -> Self {
        RichVar {
            var_name: name.to_string(),
            var_type_id: type_id,
            member_access,
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

                return RichVar {
                    var_name: var.var_name.clone(),
                    var_type_id: TypeId::unknown(),
                    member_access: None,
                };
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

    /// Attempts to find the type ID of a variable given the variable name.
    fn get_type_id_by_var_name(
        ctx: &ProgramContext,
        name: &str,
        include_fns: bool,
    ) -> Option<TypeId> {
        // Search for a variable with the given name. Variables take precedence over functions.
        match ctx.get_var(name) {
            Some(typ) => {
                return Some(typ.clone());
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

        // Check if the member access is accessing a field on a struct type.
        let member_name = &member_access.member_name;
        if let RichType::Struct(struct_type) = typ {
            if let Some(field_type_id) = struct_type.get_field_type(member_name.as_str()) {
                // If a submember is being accessed, continue resolving it recursively. Otherwise,
                // just return the field type.
                return match &member_access.submember {
                    Some(submember) => {
                        let tid = field_type_id.clone();
                        let submember_access =
                            RichMemberAccess::from(ctx, &tid, submember.as_ref());
                        RichMemberAccess {
                            member_name: member_name.to_string(),
                            member_type_id: tid,
                            submember: Some(Box::new(submember_access)),
                        }
                    }
                    None => RichMemberAccess {
                        member_name: member_name.to_string(),
                        member_type_id: field_type_id.clone(),
                        submember: None,
                    },
                };
            }
        }

        ctx.add_err(AnalyzeError::new_with_locatable(
            ErrorKind::MemberNotDefined,
            format_code!("here type {} has no member {}", typ, member_name).as_str(),
            Box::new(member_access.clone()),
        ));

        RichMemberAccess {
            member_name: member_name.to_string(),
            member_type_id: TypeId::unknown(),
            submember: None,
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
}
