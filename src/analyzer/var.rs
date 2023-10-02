use std::fmt::{Display, Formatter};

use colored::Colorize;

use crate::analyzer::error::{AnalyzeError, ErrorKind};
use crate::analyzer::prog_context::{ProgramContext, ScopedVar};
use crate::analyzer::r#type::{RichType, TypeId};
use crate::lexer::pos::{Locatable, Position};
use crate::parser::member::MemberAccess;
use crate::parser::r#type::Type;
use crate::parser::var::Var;
use crate::{format_code, util};

/// Represents a variable, either by name or by access to one of its members.
#[derive(Debug, Clone)]
pub struct RichVar {
    pub var_name: String,
    /// The type ID of the parent variable (i.e. not the member(s) being accessed).
    pub var_type_id: TypeId,
    pub member_access: Option<RichMemberAccess>,
    /// This will be set to true if the name of this variable matches a type name and no variable
    /// names. If this is the case, the `var_type_id` field will hold the ID of the matching type.
    pub is_type: bool,
    /// This will be set to true if this variable actually resolves to a constant.
    pub is_const: bool,
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
            is_type: false,
            is_const: false,
            start_pos: Position::default(),
            end_pos: Position::default(),
        }
    }

    /// Attempts to analyze the variable (including member accesses). If `include_fns` is
    /// `true`, functions and extern functions will also be searched for the variable name.
    /// Otherwise, only variables will be searched.
    pub fn from(
        ctx: &mut ProgramContext,
        var: &Var,
        include_fns: bool,
        maybe_impl_type_id: Option<&TypeId>,
    ) -> Self {
        let var_name = var.var_name.as_str();

        // Find the type ID for the variable or member being accessed.
        // Return a placeholder value if we failed to resolve the variable type ID.
        let (mut maybe_type_id, maybe_var) =
            RichVar::get_type_id_by_var_name(ctx, var.var_name.as_str(), include_fns);

        if maybe_type_id.is_none() && include_fns {
            // We could not find the variable or function with the given name, so if there is
            // an impl_type_id, check if this function is defined as a member function on
            // that type.
            if let Some(impl_type_id) = maybe_impl_type_id {
                if let Some(mem_fn) = ctx.get_type_member_fn(impl_type_id, var_name) {
                    maybe_type_id = Some(mem_fn.type_id.clone());
                }
            }
        };

        // If the symbol still has not been resolved, check if it's a type.
        let mut var_is_type = false;
        if maybe_type_id.is_none() {
            let type_id = TypeId::from(Type::new_unknown(var_name));
            if ctx.get_resolved_type(&type_id).is_some() {
                maybe_type_id = Some(type_id);
                var_is_type = true;
            }
        }

        // At this point the symbol must be resolved, or it doesn't exist in this scope.
        let var_type_id = match maybe_type_id {
            Some(t) => t,
            None => {
                // We could not find the variable or function with the given name, so record the
                // error and return a placeholder value.
                ctx.add_err(AnalyzeError::new(
                    ErrorKind::SymbolNotDefined,
                    format_code!("{} is not defined in this scope", var_name).as_str(),
                    var,
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
            Some(access) => Some(RichMemberAccess::from(ctx, &var_type_id, access)),
            None => None,
        };

        // Check if this var is actually a constant.
        let is_const = match maybe_var {
            Some(var) => var.is_const,
            None => false,
        };

        RichVar {
            var_name: var_name.to_string(),
            var_type_id,
            member_access,
            is_type: var_is_type,
            is_const,
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

    /// Attempts to find the type ID of a symbol with the given name. Additionally, if `name`
    /// can be resolved to an actual variable, the variable will be returned.
    fn get_type_id_by_var_name(
        ctx: &ProgramContext,
        name: &str,
        include_fns: bool,
    ) -> (Option<TypeId>, Option<ScopedVar>) {
        // Search for a variable with the given name. Variables take precedence over functions.
        match ctx.get_var(name) {
            Some(var) => {
                return (Some(var.type_id.clone()), Some(var.clone()));
            }
            None => {}
        }

        if include_fns {
            // Search for a function with the given name. Functions take precedence over extern
            // functions.
            match ctx.get_fn(name) {
                Some(func) => return (Some(func.signature.type_id.clone()), None),
                None => {}
            };

            // Search for an extern function with the given name. Extern functions take precedence over
            // types.
            match ctx.get_extern_fn(name) {
                Some(fn_sig) => return (Some(fn_sig.type_id.clone()), None),
                None => (None, None),
            }
        } else {
            (None, None)
        }
    }

    /// Removes the last member on this member access chain, or does nothing if there are no
    /// members.
    pub fn without_last_member(mut self) -> Self {
        if let Some(member_access) = &mut self.member_access {
            if member_access.submember.is_none() {
                self.member_access = None;
            } else {
                self.member_access = Some(self.member_access.unwrap().without_last_member());
            }
        }

        self
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

        // If we failed to find a field on this type with a matching name, check for a member
        // function with a matching name.
        let maybe_field_type_id = if maybe_field_type_id.is_none() {
            match ctx.get_type_member_fn(type_id, member_name) {
                Some(member_fn_sig) => Some(&member_fn_sig.type_id),
                None => None,
            }
        } else {
            maybe_field_type_id
        };

        // Error and return a placeholder value if we couldn't locate the member being accessed.
        if maybe_field_type_id.is_none() {
            ctx.add_err(AnalyzeError::new(
                ErrorKind::MemberNotDefined,
                format_code!("type {} has no member {}", typ, member_name).as_str(),
                member_access,
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

    /// Removes the last member on this member access chain, or does nothing if there is no
    /// sub-member.
    pub fn without_last_member(mut self) -> Self {
        if let Some(sub) = &mut self.submember {
            if sub.submember.is_none() {
                self.submember = None;
            } else {
                self.submember = Some(Box::new(self.submember.unwrap().without_last_member()));
            }
        }

        self
    }
}
