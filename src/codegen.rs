use std::collections::HashMap;
use std::fmt;
use std::str::FromStr;

use cranelift::prelude::*;
use cranelift_codegen::ir::UserFuncName;
use cranelift_codegen::isa::{Builder, OwnedTargetIsa};
use cranelift_codegen::settings::{builder, Flags};
use cranelift_codegen::{ir, verify_function};
use log::debug;
use target_lexicon::Triple;

use crate::analyzer::closure::RichClosure;
use crate::analyzer::cond::{RichCond};
use crate::analyzer::expr::{RichExpr, RichExprKind};
use crate::analyzer::func::{RichFn, RichRet};
use crate::analyzer::program::RichProg;
use crate::analyzer::statement::RichStatement;
use crate::analyzer::var_dec::RichVarDecl;




use crate::parser::func_sig::FunctionSignature;
use crate::parser::op::Operator;

use crate::parser::r#type::Type;



/// Represents kinds of errors that happen during IR generation.
enum IRGenErrorKind {
    InitFailure,
    FnVerificationFailed,
}

impl fmt::Display for IRGenErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            IRGenErrorKind::InitFailure => write!(f, "initialization failure"),
            IRGenErrorKind::FnVerificationFailed => write!(f, "function verification failed"),
        }
    }
}

/// Represents errors that happen during IR generation.
pub struct IRGenError {
    kind: IRGenErrorKind,
    message: String,
}

impl fmt::Display for IRGenError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "IR generation error: {}: {}", self.kind, self.message)
    }
}

impl IRGenError {
    fn new(kind: IRGenErrorKind, message: &str) -> Self {
        IRGenError {
            kind,
            message: message.to_string(),
        }
    }
}

/// Represents the result of IR generation.
type IRGenResult<T> = Result<T, IRGenError>;

/// Represents functions for which IR has been generated.
struct GenFn {
    index: u32,
    sig: FunctionSignature,
}

impl GenFn {
    fn new(index: u32, sig: FunctionSignature) -> Self {
        GenFn { index, sig }
    }
}

/// Generates IR for functions.
struct FnGenerator<'a> {
    vars: HashMap<String, Variable>,
    fn_builder: FunctionBuilder<'a>,
    var_counter: usize,
}

impl FnGenerator<'_> {
    /// Returns a new variable identifier that is unique within the current function.
    fn next_var(&mut self) -> usize {
        self.var_counter += 1;
        self.var_counter - 1
    }

    /// Returns a new variable.
    fn new_var(&mut self) -> Variable {
        Variable::new(self.next_var())
    }

    /// Generates IR for a statement in the current function.
    fn gen_statement(&mut self, statement: &RichStatement) -> IRGenResult<()> {
        match statement {
            // TODO
            // Statement::FunctionDeclaration(func) => self.gen_fn(func),
            RichStatement::VariableDeclaration(var_decl) => self.gen_var_decl(var_decl),
            RichStatement::Return(expr) => self.gen_return(expr),
            RichStatement::Conditional(cond) => self.gen_cond(cond),
            other => {
                return Err(IRGenError::new(
                    IRGenErrorKind::InitFailure,
                    format!("unimplemented {}", other).as_str(),
                ))
            }
        }
    }

    /// Generates IR for a conditional in the current function.
    fn gen_cond(&mut self, rich_cond: &RichCond) -> IRGenResult<()> {
        // Create an end block that we can jump to one we're done executing the branch.
        let end_block = self.fn_builder.create_block();

        for branch in &rich_cond.branches {
            if let Some(branch_cond) = &branch.cond {
                // Generate the condition variable and the two blocks that we'll branch to based
                // on the condition.
                let cond_var = self.gen_expr(branch_cond);
                let then_block = self.fn_builder.create_block();
                let else_block = self.fn_builder.create_block();

                // Create the branch instruction that will jump to one of the two blocks based
                // on the condition.
                self.fn_builder
                    .ins()
                    .brif(cond_var, then_block, &[], else_block, &[]);

                // Seal the blocks since there should be nothing else that branches/jumps to them.
                self.fn_builder.seal_block(then_block);
                self.fn_builder.seal_block(else_block);

                // Fill the then block.
                self.fn_builder.switch_to_block(then_block);
                if let Err(e) = self.gen_closure(&branch.body, end_block) {
                    return Err(e);
                }

                // Continue on the else block.
                self.fn_builder.switch_to_block(else_block);
            } else {
                // There is no branch condition, meaning this is the else case, so we must jump to
                // the then block.
                let then_block = self.fn_builder.create_block();
                self.fn_builder.ins().jump(then_block, &[]);

                // Seal the then block because nothing else will jump/branch to it.
                self.fn_builder.seal_block(then_block);

                // Continue on the then block.
                self.fn_builder.switch_to_block(then_block);

                // Generate instructions for end closure.
                if let Err(e) = self.gen_closure(&branch.body, end_block) {
                    return Err(e);
                }
            }
        }

        // Seal the end block before returning, because we know nothing else will branch/jump to it.
        self.fn_builder.seal_block(end_block);

        // Continue on the end block.
        self.fn_builder.switch_to_block(end_block);

        Ok(())
    }

    /// Generates IR for a closure in the current function. Note that closures can be inline,
    /// branch bodies, or loop bodies.
    fn gen_closure(&mut self, closure: &RichClosure, end_block: Block) -> IRGenResult<()> {
        let mut returned = false;
        for statement in &closure.statements {
            if let Err(e) = self.gen_statement(statement) {
                return Err(e);
            }

            if let RichStatement::Return(_) = statement {
                returned = true
            }
        }

        // We must either return or jump to another block at the end of the closure.
        if !returned {
            self.fn_builder.ins().jump(end_block, &[]);
        }

        Ok(())
    }

    /// Generates IR for return statements in the function.
    fn gen_return(&mut self, rich_ret: &RichRet) -> IRGenResult<()> {
        if let Some(val) = &rich_ret.val {
            let ret_val = self.gen_expr(val);
            self.fn_builder.ins().return_(&[ret_val]);
        } else {
            self.fn_builder.ins().return_(&[]);
        }

        Ok(())
    }

    /// Generates IR for variable declarations in the function.
    fn gen_var_decl(&mut self, var_decl: &RichVarDecl) -> IRGenResult<()> {
        // Create a new variable.
        let var = self.new_var();

        // Declare the variable type.
        self.declare_var(var, &var_decl.typ);

        // Define the variable with its initial value.
        self.def_var(var, &var_decl.val);

        // Track the variable so we can reference it later.
        self.vars.insert(var_decl.name.clone(), var);

        Ok(())
    }

    /// Generates IR for unary operations in the function.
    fn gen_unary_op(&mut self, op: &Operator, expr: &RichExpr) -> Value {
        let val = self.gen_expr(expr);
        match op {
            Operator::Not => {
                // Make sure the boolean value is either all 0s (representing false) or all 1s
                // (representing true).
                let tmp = self.fn_builder.ins().bmask(ir::types::I8, val);
                // Bitwise not to flip all the bits.
                self.fn_builder.ins().bnot(tmp)
            }
            _ => panic!("invalid unary operator {}", op),
        }
    }

    /// Generates IR for binary operations in the function.
    fn gen_binary_op(&mut self, left: &RichExpr, op: &Operator, right: &RichExpr) -> Value {
        let left_val = self.gen_expr(left);
        let right_val = self.gen_expr(right);

        match op {
            Operator::Add => self.fn_builder.ins().iadd(left_val, right_val),
            Operator::Subtract => self.fn_builder.ins().isub(left_val, right_val),
            Operator::Multiply => self.fn_builder.ins().imul(left_val, right_val),
            Operator::Divide => self.fn_builder.ins().udiv(left_val, right_val),
            Operator::Modulo => self.fn_builder.ins().urem(left_val, right_val),
            Operator::LogicalAnd => self.fn_builder.ins().band(left_val, right_val),
            Operator::LogicalOr => self.fn_builder.ins().bor(left_val, right_val),
            // TODO: handle comparators based on operand types
            // Operator::EqualTo =>
            // Operator::NotEqualTo =>
            Operator::GreaterThan => {
                self.fn_builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThan, left_val, right_val)
            }
            Operator::LessThan => {
                self.fn_builder
                    .ins()
                    .icmp(IntCC::SignedLessThan, left_val, right_val)
            }
            Operator::GreaterThanOrEqual => {
                self.fn_builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThanOrEqual, left_val, right_val)
            }
            Operator::LessThanOrEqual => {
                self.fn_builder
                    .ins()
                    .icmp(IntCC::SignedLessThanOrEqual, left_val, right_val)
            }
            other => panic!("unimplemented binary operator {}", other),
        }
    }

    /// Generates IR for expressions in the function.
    fn gen_expr(&mut self, expr: &RichExpr) -> Value {
        match &expr.kind {
            RichExprKind::BoolLiteral(b) => self.gen_bool_literal(*b),
            RichExprKind::I64Literal(i) => self.gen_i64_literal(*i),
            RichExprKind::BinaryOperation(left, op, right) => self.gen_binary_op(left, op, right),
            RichExprKind::UnaryOperation(op, expr) => self.gen_unary_op(op, expr),
            other => {
                panic!("unimplemented expression {}", other)
            }
        }
    }

    /// Generates IR for the function body.
    fn gen_fn_body(&mut self, rich_fn: &RichFn) -> IRGenResult<()> {
        // Create the entry block, to start emitting code in.
        let block0 = self.fn_builder.create_block();

        // Since this is the entry block, add block parameters corresponding to the function's
        // parameters.
        self.fn_builder
            .append_block_params_for_function_params(block0);

        // Tell the builder to emit code in this block.
        self.fn_builder.switch_to_block(block0);

        // Seal the block since nothing else can jump to it.
        self.fn_builder.seal_block(block0);

        // Generate IR for statements.
        let mut returned = false;
        for statement in &rich_fn.closure.statements {
            if let Err(e) = self.gen_statement(statement) {
                return Err(e);
            }

            if let RichStatement::Return(_) = statement {
                returned = true
            }
        }

        // Generate a return instruction if the source code didn't already contain a return.
        if !returned {
            self.fn_builder.ins().return_(&[]);
        }

        Ok(())
    }

    /// Defines the initial value of the given variable from the given expression using the function
    /// builder.
    fn def_var(&mut self, var: Variable, expr: &RichExpr) {
        let val = self.gen_expr(expr);
        self.fn_builder.def_var(var, val);
    }

    /// Declares the type of the given variable using the function builder.
    fn declare_var(&mut self, var: Variable, typ: &Type) {
        let typ = gen_type(typ);
        self.fn_builder.declare_var(var, typ);
    }

    /// Generates an i64 literal with the given value using the function builder.
    fn gen_i64_literal(&mut self, i: i64) -> Value {
        self.fn_builder.ins().iconst(gen_type(&Type::I64), i)
    }

    /// Generates a bool literal (represented as i8 because Cranelift doesn't have bools) with the
    /// given value using the function builder.
    fn gen_bool_literal(&mut self, b: bool) -> Value {
        let val = match b {
            true => 1,
            false => 0,
        };
        self.fn_builder.ins().iconst(gen_type(&Type::Bool), val)
    }
}

/// Generates IR for a program.
pub struct IRGenerator {
    target_isa: OwnedTargetIsa,
    /// Tracks functions for which IR has been generated.
    gen_fns: HashMap<String, GenFn>,
    /// Represents the index of the next function to be generated.
    fn_counter: u32,
    /// Stores IR generator settings.
    flags: Flags,
}

impl IRGenerator {
    /// Creates a new IR generator configured for the target ISA.
    pub fn new_for_target(target_triple: &str) -> IRGenResult<Self> {
        let target_triple = match Triple::from_str(target_triple) {
            Ok(t) => t,
            Err(e) => {
                return Err(IRGenError::new(
                    IRGenErrorKind::InitFailure,
                    format!("failed to initialize target triple: {}", e).as_str(),
                ));
            }
        };

        let isa_builder = match isa::lookup(target_triple.clone()) {
            Ok(b) => b,
            Err(e) => {
                return Err(IRGenError::new(
                    IRGenErrorKind::InitFailure,
                    format!(
                        "failed to look up ISA builder for target {}: {}",
                        target_triple, e
                    )
                    .as_str(),
                ));
            }
        };

        IRGenerator::new_for_isa(isa_builder)
    }

    /// Creates a new IR generator configured for the host system.
    pub fn new() -> IRGenResult<Self> {
        let mut isa_builder = match cranelift_native::builder() {
            Ok(builder) => builder,
            Err(err) => {
                return Err(IRGenError::new(
                    IRGenErrorKind::InitFailure,
                    format!("failed to initialize ISA builder {}", err).as_str(),
                ));
            }
        };

        if let Err(e) = cranelift_native::infer_native_flags(&mut isa_builder) {
            return Err(IRGenError::new(
                IRGenErrorKind::InitFailure,
                format!("failed to infer native flags: {}", e).as_str(),
            ));
        }

        IRGenerator::new_for_isa(isa_builder)
    }

    /// Creates a new IR generator from the given ISA builder.
    fn new_for_isa(isa_builder: Builder) -> IRGenResult<Self> {
        let flags = Flags::new(builder());
        let target_isa = match isa_builder.finish(flags.clone()) {
            Ok(i) => i,
            Err(e) => {
                return Err(IRGenError::new(
                    IRGenErrorKind::InitFailure,
                    format!("failed to finish building ISA: {}", e).as_str(),
                ))
            }
        };

        Ok(IRGenerator {
            target_isa,
            gen_fns: HashMap::new(),
            fn_counter: 0,
            flags,
        })
    }

    /// Generates IR for the given program.
    pub fn gen_prog(&mut self, prog: RichProg) -> IRGenResult<()> {
        // Generate IR for each statement in the program.
        for statement in prog.statements {
            if let Err(e) = match statement {
                RichStatement::FunctionDeclaration(func) => self.gen_fn(&func),
                other => {
                    panic!("unimplemented top-level statement: {}", other);
                }
            } {
                return Err(e);
            }
        }

        Ok(())
    }

    /// Generates IR for a new function.
    fn gen_fn(&mut self, rich_fn: &RichFn) -> IRGenResult<()> {
        // Generate the function signature.
        let sig = self.gen_fn_sig(&rich_fn.signature);

        // Create a new function with the signature.
        let fn_index = self.next_fn();
        let mut new_func = ir::Function::with_name_signature(UserFuncName::user(0, fn_index), sig);

        // Create a new function builder that we'll use to build this function.
        let mut fn_builder_ctx = FunctionBuilderContext::new();
        let fn_builder = FunctionBuilder::new(&mut new_func, &mut fn_builder_ctx);
        let mut fn_gen = FnGenerator {
            vars: HashMap::new(),
            fn_builder,
            var_counter: 0,
        };

        // Generate the function body.
        if let Err(e) = fn_gen.gen_fn_body(rich_fn) {
            return Err(e);
        }

        // Tell the builder we're done with this function.
        fn_gen.fn_builder.finalize();

        // Verify the function.
        if let Err(e) = verify_function(&new_func, &self.flags) {
            return Err(IRGenError::new(
                IRGenErrorKind::FnVerificationFailed,
                e.to_string().as_str(),
            ));
        }

        // Track the generated function so we can reference it later.
        self.gen_fns.insert(
            rich_fn.signature.name.clone(),
            GenFn::new(fn_index, rich_fn.signature.clone()),
        );

        debug!(
            "generated IR for function {}:\n{}",
            &rich_fn.signature.name,
            new_func.display()
        );
        Ok(())
    }

    /// Creates a function signature.
    fn gen_fn_sig(&mut self, sig: &FunctionSignature) -> Signature {
        // Define the function signature.
        let mut fn_sig = Signature::new(self.target_isa.default_call_conv());

        // Add the function argument types.
        for arg in &sig.args {
            fn_sig.params.push(gen_abi_param(&arg.typ));
        }

        // Add the return type, if there is one.
        if sig.return_type.is_some() {
            fn_sig
                .returns
                .push(gen_abi_param(sig.return_type.as_ref().unwrap()));
        }

        fn_sig
    }

    /// Returns the next function identifier.
    fn next_fn(&mut self) -> u32 {
        self.fn_counter += 1;
        self.fn_counter - 1
    }
}

/// Creates an ABI parameter with the given type.
fn gen_abi_param(typ: &Type) -> AbiParam {
    AbiParam::new(gen_type(typ))
}

/// Converts the given type into a Cranelift type.
fn gen_type(typ: &Type) -> types::Type {
    match typ {
        // Cranelift doesn't have boolean types, so we use i8.
        Type::Bool => types::I8,
        Type::I64 => types::I64,
        other => panic!("unimplemented type {}", other),
    }
}
