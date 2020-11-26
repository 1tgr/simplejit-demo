use crate::ast::*;
use crate::frontend::{ArithmeticKind, ComparisonKind};
use crate::lower::Lower;
use crate::parse::Parse;
use crate::target::{Target, TargetExt};
use crate::type_ck::TypeCk;
use crate::{Error, Result, VecExt};
use cranelift::codegen::binemit::NullTrapSink;
use cranelift::codegen::entity::EntityRef;
use cranelift::codegen::ir::condcodes::IntCC;
use cranelift::codegen::ir::types::{self, Type as ClType};
use cranelift::codegen::ir::{AbiParam, FuncRef as ClFuncRef, GlobalValue as ClGlobalValue, InstBuilder, MemFlags, Signature as ClSignature, Value};
use cranelift::codegen::isa::CallConv;
use cranelift::codegen::verifier::VerifierErrors;
use cranelift::codegen::{CodegenError, Context as ClContext};
use cranelift::frontend::{FunctionBuilder, FunctionBuilderContext, Variable as ClVariable};
use cranelift_module::{DataId as ClDataId, FuncId as ClFuncId, Linkage, Module as _, ModuleError};
use std::collections::HashMap;
use std::ops;
use std::rc::Rc;
use std::slice;

#[derive(Clone)]
pub struct Context(Rc<ClContext>);

impl PartialEq for Context {
    #[allow(clippy::vtable_address_comparisons)]
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for Context {}

impl ops::Deref for Context {
    type Target = ClContext;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[salsa::query_group(JITDatabase)]
pub trait JIT: Parse + Lower + Target + TypeCk {
    fn cl_pointer_type(&self) -> ClType;
    fn cl_default_call_conv(&self) -> CallConv;
    fn cl_type(&self, ty: TypeId) -> Option<ClType>;
    fn cl_signature(&self, signature: Signature) -> ClSignature;
    fn cl_func_id(&self, external: bool, name: IdentId, signature: Signature) -> Result<ClFuncId>;
    fn cl_data_id(&self, name: IdentId) -> Result<ClDataId>;
    fn cl_ctx(&self, name: IdentId) -> Result<Context>;
}

fn cl_pointer_type(db: &dyn JIT) -> ClType {
    db.with_module(|module| module.target_config().pointer_type())
}

fn cl_default_call_conv(db: &dyn JIT) -> CallConv {
    db.with_module(|module| module.isa().default_call_conv())
}

fn cl_type(db: &dyn JIT, ty: TypeId) -> Option<ClType> {
    match db.lookup_intern_type(ty) {
        Type::Bool => Some(types::B1),
        Type::Integer(ty) => {
            let Integer { signed: _signed, bits } = ty;
            Some(ClType::int(bits).unwrap())
        }
        Type::Number => panic!("didn't expect number type to survive unification"),
        Type::Pointer(_) => Some(db.cl_pointer_type()),
        Type::Var(_) => panic!("didn't expect type variable to survive unification"),
        Type::Unit => None,
    }
}

fn cl_signature(db: &dyn JIT, signature: Signature) -> ClSignature {
    let Signature { param_tys, return_ty } = signature;
    let mut sig = ClSignature::new(db.cl_default_call_conv());
    sig.params = param_tys.into_iter().map(|ty| AbiParam::new(db.cl_type(ty).unwrap())).collect();

    if let Some(return_ty) = db.cl_type(return_ty) {
        sig.returns.push(AbiParam::new(return_ty));
    }

    sig
}

fn cl_func_id(db: &dyn JIT, external: bool, name: IdentId, signature: Signature) -> Result<ClFuncId> {
    let name = db.lookup_intern_ident(name);
    let signature = db.cl_signature(signature);
    let linkage = if external { Linkage::Import } else { Linkage::Export };
    db.with_module_mut(|module| Ok(module.declare_function(&name, linkage, &signature)?))
}

fn cl_data_id(db: &dyn JIT, name: IdentId) -> Result<ClDataId> {
    let name = db.lookup_intern_ident(name);
    db.with_module_mut(|module| Ok(module.declare_data(&name, Linkage::Export, true, false)?))
}

fn cl_ctx(db: &dyn JIT, name: IdentId) -> Result<Context> {
    let signature = db.function_signature(name)?;
    let body = db.lower_function(name)?;
    let mut ctx = ClContext::new();
    ctx.func.signature = db.cl_signature(signature.clone());

    let func_ctx_pool = db.func_ctx_pool();
    let mut func_ctx = func_ctx_pool.pull(FunctionBuilderContext::new);
    func_ctx.clear();

    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut func_ctx);

    let param_values = {
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);
        builder.block_params(entry_block).to_vec()
    };

    let expr_types = db.unify_function(name)?;
    let return_value = FunctionTranslator::new(db, &mut builder, param_values, &expr_types).map_expr(body)?;
    builder.ins().return_(return_value.as_ref().map_or(&[], slice::from_ref));
    builder.finalize();

    let func = db.cl_func_id(false, name, signature)?;
    db.with_module_mut(|module| {
        module.define_function(func, &mut ctx, &mut NullTrapSink {}).map_err(|mut e| {
            if let ModuleError::Compilation(CodegenError::Verifier(VerifierErrors(v))) = &mut e {
                if let Some(e) = v.as_single_item() {
                    return Error::from(e);
                }
            }

            Error::from(e)
        })?;

        Ok(Context(Rc::new(ctx)))
    })
}

struct FunctionTranslator<'a, 'b> {
    db: &'a dyn JIT,
    builder: &'a mut FunctionBuilder<'b>,
    param_values: Vec<Value>,
    expr_types: &'a HashMap<ExprId, TypeId>,
    cl_variables: HashMap<(EnvId, IdentId), Option<ClVariable>>,
    cl_functions: HashMap<(EnvId, IdentId), ClFuncRef>,
    cl_data: HashMap<ClDataId, ClGlobalValue>,
}

impl<'a, 'b> FunctionTranslator<'a, 'b> {
    fn new(db: &'a dyn JIT, builder: &'a mut FunctionBuilder<'b>, param_values: Vec<Value>, expr_types: &'a HashMap<ExprId, TypeId>) -> Self {
        Self {
            db,
            builder,
            param_values,
            expr_types,
            cl_variables: HashMap::new(),
            cl_functions: HashMap::new(),
            cl_data: HashMap::new(),
        }
    }

    fn translate_variable(&mut self, env: EnvId, name: IdentId) -> Option<ClVariable> {
        let Env { bindings } = self.db.lookup_intern_env(env);
        let &(decl_env, ref binding) = &bindings[&name];

        if let Some(&variable) = self.cl_variables.get(&(decl_env, name)) {
            return variable;
        }

        let (value, ty) = match binding {
            Binding::Param(binding) => {
                let &Param { index, ty } = binding;
                (Some(self.param_values[index]), ty)
            }

            Binding::Variable(binding) => {
                let &Variable { decl_expr } = binding;
                (None, self.expr_types[&decl_expr])
            }

            Binding::Extern(_) | Binding::Function(_) => panic!("functions can only be called"),
        };

        let variable = self.db.cl_type(ty).map(|ty| {
            let variable = ClVariable::new(self.cl_variables.len());
            self.builder.declare_var(variable, ty);

            if let Some(value) = value {
                self.builder.def_var(variable, value);
            }

            variable
        });

        self.cl_variables.insert((decl_env, name), variable);
        variable
    }
}

impl<'a, 'b> ExprMap for FunctionTranslator<'a, 'b> {
    type Value = Result<Option<Value>>;

    fn lookup_expr(&self, expr: ExprId) -> Expr {
        self.db.lookup_intern_expr(expr)
    }

    fn map_arithmetic(&mut self, _expr_id: ExprId, expr: Arithmetic) -> Result<Option<Value>> {
        let Arithmetic { lhs, op, rhs } = expr;
        let lhs = self.map_expr(lhs)?.unwrap();
        let rhs = self.map_expr(rhs)?.unwrap();

        let value = match op {
            ArithmeticKind::Add => self.builder.ins().iadd(lhs, rhs),
            ArithmeticKind::Sub => self.builder.ins().isub(lhs, rhs),
            ArithmeticKind::Mul => self.builder.ins().imul(lhs, rhs),
            ArithmeticKind::Div => self.builder.ins().udiv(lhs, rhs),
        };

        Ok(Some(value))
    }

    fn map_assign(&mut self, _expr_id: ExprId, expr: Assign) -> Result<Option<Value>> {
        let Assign { lvalue, expr } = expr;
        let value = self.map_expr(expr)?;

        match self.db.lookup_intern_expr(lvalue) {
            Expr::Deref(expr) => {
                let Deref { expr } = expr;
                let ptr_value = self.map_expr(expr)?.unwrap();
                if let Some(value) = value {
                    self.builder.ins().store(MemFlags::new(), value, ptr_value, 0);
                }
            }

            Expr::Identifier(expr) => {
                let Identifier { env, name } = expr;
                if let Some(value) = value {
                    let variable = self.translate_variable(env, name).unwrap();
                    self.builder.def_var(variable, value);
                }
            }

            Expr::Index(expr) => {
                let Index { base, offset } = expr;
                let base_value = self.map_expr(base)?.unwrap();
                let offset_value = self.map_expr(offset)?.unwrap();
                let ptr_value = self.builder.ins().iadd(base_value, offset_value);
                if let Some(value) = value {
                    self.builder.ins().store(MemFlags::new(), value, ptr_value, 0);
                }
            }

            _ => unreachable!(),
        }

        Ok(value)
    }

    fn map_block(&mut self, _expr_id: ExprId, expr: Block) -> Result<Option<Value>> {
        let Block { stmts } = expr;

        let mut value = None;
        for expr in stmts {
            value = self.map_expr(expr)?;
        }

        Ok(value)
    }

    fn map_call(&mut self, expr_id: ExprId, expr: Call) -> Result<Option<Value>> {
        let Call { env, name, args } = expr;
        let Env { bindings } = self.db.lookup_intern_env(env);
        let &(decl_env, ref binding) = &bindings[&name];

        let func = match binding.clone() {
            Binding::Extern(signature) => self.db.cl_func_id(true, name, signature)?,
            Binding::Function(signature) => self.db.cl_func_id(false, name, signature)?,
            Binding::Param(_) | Binding::Variable(_) => panic!("only functions can be called"),
        };

        let local_callee = {
            let Self { db, builder, cl_functions, .. } = self;
            *cl_functions
                .entry((decl_env, name))
                .or_insert_with(|| db.with_module_mut(|module| module.declare_func_in_func(func, &mut builder.func)))
        };

        let arg_values = args
            .into_iter()
            .map(|expr| {
                let value = self.map_expr(expr)?;
                Ok(value.unwrap())
            })
            .collect::<Result<Vec<_>>>()?;

        let call = self.builder.ins().call(local_callee, &arg_values);
        let ty = self.db.cl_type(self.expr_types[&expr_id]);
        Ok(ty.map(|_| self.builder.inst_results(call)[0]))
    }

    fn map_comparison(&mut self, _expr_id: ExprId, expr: Comparison) -> Result<Option<Value>> {
        let Comparison { lhs, op, rhs } = expr;
        let lhs = self.map_expr(lhs)?.unwrap();
        let rhs = self.map_expr(rhs)?.unwrap();

        let cc = match op {
            ComparisonKind::Eq => IntCC::Equal,
            ComparisonKind::Ne => IntCC::NotEqual,
            ComparisonKind::Lt => IntCC::SignedLessThan,
            ComparisonKind::Le => IntCC::SignedLessThanOrEqual,
            ComparisonKind::Gt => IntCC::SignedGreaterThan,
            ComparisonKind::Ge => IntCC::SignedGreaterThanOrEqual,
        };

        Ok(Some(self.builder.ins().icmp(cc, lhs, rhs)))
    }

    fn map_deref(&mut self, _expr_id: ExprId, expr: Deref) -> Result<Option<Value>> {
        let Deref { expr: _expr } = expr;
        todo!()
    }

    fn map_global_data_addr(&mut self, expr_id: ExprId, expr: GlobalDataAddr) -> Result<Option<Value>> {
        let GlobalDataAddr { name } = expr;
        let Self { db, builder, cl_data, .. } = self;
        let data = db.cl_data_id(name)?;

        let local_id = *cl_data
            .entry(data)
            .or_insert_with(|| db.with_module_mut(|module| module.declare_data_in_func(data, &mut builder.func)));

        let ty = self.db.cl_type(self.expr_types[&expr_id]);
        Ok(Some(builder.ins().symbol_value(ty.unwrap(), local_id)))
    }

    fn map_identifier(&mut self, _expr_id: ExprId, expr: Identifier) -> Result<Option<Value>> {
        let Identifier { env, name } = expr;
        Ok(self.translate_variable(env, name).map(|variable| self.builder.use_var(variable)))
    }

    fn map_if_else(&mut self, expr_id: ExprId, expr: IfElse) -> Result<Option<Value>> {
        let IfElse { condition, then_body, else_body } = expr;
        let condition_value = self.map_expr(condition)?.unwrap();

        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        let value = self.db.cl_type(self.expr_types[&expr_id]).map(|ty| {
            self.builder.append_block_param(merge_block, ty);
            self.builder.block_params(merge_block)[0]
        });

        self.builder.ins().brz(condition_value, else_block, &[]);
        self.builder.ins().jump(then_block, &[]);

        self.builder.switch_to_block(then_block);
        self.builder.seal_block(then_block);

        let then_return = self.map_expr(then_body)?;
        self.builder.ins().jump(merge_block, then_return.as_ref().map_or(&[], slice::from_ref));

        self.builder.switch_to_block(else_block);
        self.builder.seal_block(else_block);

        let else_return = self.map_expr(else_body)?;
        self.builder.ins().jump(merge_block, else_return.as_ref().map_or(&[], slice::from_ref));

        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);
        Ok(value)
    }

    fn map_index(&mut self, _expr_id: ExprId, expr: Index) -> Result<Option<Value>> {
        let Index { base: _base, offset: _offset } = expr;
        todo!()
    }

    fn map_literal(&mut self, expr_id: ExprId, expr: Literal) -> Result<Option<Value>> {
        let Literal { value } = expr;
        let ty = self.db.cl_type(self.expr_types[&expr_id]);
        Ok(Some(self.builder.ins().iconst(ty.unwrap(), i64::from(value))))
    }

    fn map_scope(&mut self, _expr_id: ExprId, expr: Scope) -> Result<Option<Value>> {
        let Scope { scope_env, name, body } = expr;
        let Env { bindings } = self.db.lookup_intern_env(scope_env);

        if let (_, Binding::Variable(variable)) = &bindings[&name] {
            let &Variable { decl_expr } = variable;
            if let Some(value) = self.map_expr(decl_expr)? {
                let variable = self.translate_variable(scope_env, name).unwrap();
                self.builder.def_var(variable, value);
            }
        }

        self.map_expr(body)
    }

    fn map_while_loop(&mut self, _expr_id: ExprId, expr: WhileLoop) -> Result<Option<Value>> {
        let WhileLoop { condition, body } = expr;
        let header_block = self.builder.create_block();
        let body_block = self.builder.create_block();
        let exit_block = self.builder.create_block();

        self.builder.ins().jump(header_block, &[]);
        self.builder.switch_to_block(header_block);

        let condition_value = self.map_expr(condition)?.unwrap();
        self.builder.ins().brz(condition_value, exit_block, &[]);
        self.builder.ins().jump(body_block, &[]);

        self.builder.switch_to_block(body_block);
        self.builder.seal_block(body_block);

        self.map_expr(body)?;
        self.builder.ins().jump(header_block, &[]);

        self.builder.switch_to_block(exit_block);
        self.builder.seal_block(header_block);
        self.builder.seal_block(exit_block);
        Ok(None)
    }
}
