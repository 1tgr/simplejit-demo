use crate::ast::*;
use crate::frontend::{ArithmeticKind, ComparisonKind};
use crate::lower::{Lower, LowerExt};
use crate::parse::{Parse, ParseExt};
use crate::target::{Target, TargetExt};
use crate::type_ck::TypeCk;
use crate::{Error, ProcessResultsExt, Result, VecExt, VecMapExt};
use cranelift::codegen::binemit::NullTrapSink;
use cranelift::codegen::entity::EntityRef;
use cranelift::codegen::ir::condcodes::IntCC;
use cranelift::codegen::ir::types::{self, Type as ClifType};
use cranelift::codegen::ir::{AbiParam, FuncRef as ClifFuncRef, GlobalValue as ClifGlobalValue, InstBuilder, MemFlags, Signature as ClifSignature, Value as ClifValue};
use cranelift::codegen::isa::CallConv;
use cranelift::codegen::verifier::VerifierErrors;
use cranelift::codegen::{CodegenError, Context as ClifContext};
use cranelift::frontend::{FunctionBuilder, FunctionBuilderContext, Variable as ClifVariable};
use cranelift_module::{DataId as ClifDataId, FuncId as ClifFuncId, Linkage, Module, ModuleError};
use std::collections::HashMap;
use std::convert::TryInto;
use std::ops::{self, Range};
use std::rc::Rc;

#[derive(Clone)]
pub struct Context(Rc<ClifContext>);

impl PartialEq for Context {
    #[allow(clippy::vtable_address_comparisons)]
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for Context {}

impl ops::Deref for Context {
    type Target = ClifContext;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[salsa::query_group(JITDatabase)]
pub trait Jit: Parse + Lower + Target + TypeCk {
    fn clif_pointer_type(&self) -> ClifType;
    fn clif_default_call_conv(&self) -> CallConv;
    fn clif_type(&self, ty: TypeId) -> Result<Vec<ClifType>>;
    fn clif_struct_field_range(&self, field_tys: Vec<TypeId>, field_index: usize) -> Result<Range<usize>>;
    fn clif_signature(&self, signature: Signature) -> Result<ClifSignature>;
    fn clif_func_id(&self, external: bool, name: IdentId, signature: Signature) -> Result<ClifFuncId>;
    fn clif_data_id(&self, name: IdentId) -> Result<ClifDataId>;
    fn clif_ctx(&self, function_name: IdentId) -> Result<Context>;
}

fn clif_pointer_type(db: &dyn Jit) -> ClifType {
    db.with_module(|module| module.target_config().pointer_type())
}

fn clif_default_call_conv(db: &dyn Jit) -> CallConv {
    db.with_module(|module| module.isa().default_call_conv())
}

fn clif_type(db: &dyn Jit, ty: TypeId) -> Result<Vec<ClifType>> {
    match db.lookup_intern_type(ty) {
        Type::Bool => Ok(vec![types::B1]),
        Type::Integer(ty) => {
            let Integer { signed: _signed, bits } = ty;
            Ok(vec![ClifType::int(bits).unwrap()])
        }
        Type::Named(ty) => {
            let ty_binding = db.ty_binding(ty)?;
            let Struct { field_names: _, field_tys } = ty_binding.try_into().unwrap();
            field_tys.into_iter().map(|ty| db.clif_type(ty)).process_results(|i| i.flatten().collect())
        }
        Type::Number => panic!("didn't expect number type to survive unification"),
        Type::Pointer(_) => Ok(vec![db.clif_pointer_type()]),
        Type::Var(_) => panic!("didn't expect type variable to survive unification"),
        Type::Unit => Ok(vec![]),
    }
}

fn clif_struct_field_range(db: &dyn Jit, field_tys: Vec<TypeId>, index: usize) -> Result<Range<usize>> {
    let mut prev_acc = 0;
    let mut acc = 0;
    for &ty in &field_tys[..index + 1] {
        let ty = db.clif_type(ty)?;
        prev_acc = acc;
        acc += ty.len();
    }

    Ok(prev_acc..acc)
}

fn clif_signature(db: &dyn Jit, signature: Signature) -> Result<ClifSignature> {
    let Signature { param_tys, return_ty } = signature;
    let call_conv = db.clif_default_call_conv();
    let params = param_tys
        .into_iter()
        .map(|ty| db.clif_type(ty))
        .process_results(|i| i.flatten().map(AbiParam::new).collect())?;

    let returns = db.clif_type(return_ty)?.map(AbiParam::new);
    Ok(ClifSignature { call_conv, params, returns })
}

fn clif_func_id(db: &dyn Jit, external: bool, name: IdentId, signature: Signature) -> Result<ClifFuncId> {
    let name = db.lookup_intern_ident(name);
    let signature = db.clif_signature(signature)?;
    let linkage = if external { Linkage::Import } else { Linkage::Export };
    db.with_module_mut(|module| Ok(module.declare_function(&name, linkage, &signature)?))
}

fn clif_data_id(db: &dyn Jit, name: IdentId) -> Result<ClifDataId> {
    let name = db.lookup_intern_ident(name);
    db.with_module_mut(|module| Ok(module.declare_data(&name, Linkage::Export, true, false)?))
}

fn clif_ctx(db: &dyn Jit, name: IdentId) -> Result<Context> {
    let signature = db.function_signature(name)?;
    let (_, body) = db.lower_function(name)?;
    let mut ctx = ClifContext::new();
    ctx.func.signature = db.clif_signature(signature.clone())?;

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
    let return_value = FunctionTranslator::new(db, name, &mut builder, param_values, &expr_types).map_expr(body)?;
    builder.ins().return_(&return_value);
    builder.finalize();

    let func = db.clif_func_id(false, name, signature)?;
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
    db: &'a dyn Jit,
    function_name: IdentId,
    builder: &'a mut FunctionBuilder<'b>,
    param_values: Vec<ClifValue>,
    expr_types: &'a HashMap<ExprId, TypeId>,
    clif_variables: HashMap<(EnvId, IdentId), Vec<ClifVariable>>,
    clif_functions: HashMap<(EnvId, IdentId), ClifFuncRef>,
    clif_data: HashMap<ClifDataId, ClifGlobalValue>,
    index: usize,
}

impl<'a, 'b> FunctionTranslator<'a, 'b> {
    fn new(db: &'a dyn Jit, function_name: IdentId, builder: &'a mut FunctionBuilder<'b>, param_values: Vec<ClifValue>, expr_types: &'a HashMap<ExprId, TypeId>) -> Self {
        Self {
            db,
            function_name,
            builder,
            param_values,
            expr_types,
            clif_variables: HashMap::new(),
            clif_functions: HashMap::new(),
            clif_data: HashMap::new(),
            index: 0,
        }
    }

    fn translate_variable(&mut self, env: EnvId, name: IdentId) -> Result<Vec<ClifVariable>> {
        let (decl_env, binding) = self.db.binding_pair(self.function_name, env, name)?;

        if let Some(variable) = self.clif_variables.get(&(decl_env, name)) {
            return Ok(variable.clone());
        }

        let (value, ty) = match binding {
            Binding::Param(binding) => {
                let Param { index, ty } = binding;
                let Signature { param_tys, return_ty: _ } = self.db.function_signature(self.function_name)?;
                let range = self.db.clif_struct_field_range(param_tys, index)?;
                (Some(self.param_values[range].to_vec()), ty)
            }

            Binding::Variable(binding) => {
                let Variable { decl_expr } = binding;
                (None, self.expr_types[&decl_expr])
            }

            Binding::Extern(_) | Binding::Function(_) => panic!("functions can only be called"),
        };

        let variable = self.db.clif_type(ty)?.map(|ty| {
            let variable = ClifVariable::new(self.index);
            self.index += 1;
            self.builder.declare_var(variable, ty);
            variable
        });

        if let Some(value) = value {
            assert_eq!(variable.len(), value.len());
            for (&variable, value) in variable.iter().zip(value) {
                self.builder.def_var(variable, value);
            }
        }

        self.clif_variables.insert((decl_env, name), variable.clone());
        Ok(variable)
    }

    fn struct_field_range(&self, struct_expr: ExprId, field_name: IdentId) -> Result<Range<usize>> {
        let ty = self.expr_types[&struct_expr];
        let ty_name = self.db.lookup_intern_type(ty).as_named().unwrap();
        let ty_binding = self.db.ty_binding(ty_name)?;
        let Struct { field_names, field_tys } = ty_binding.try_into().unwrap();
        let field_index = field_names.into_iter().position(|n| n == field_name).unwrap();
        self.db.clif_struct_field_range(field_tys, field_index)
    }

    fn translate_lvalue_dot(&mut self, expr: Dot) -> Result<Vec<ClifVariable>> {
        let Dot { expr, field_name } = expr;

        let struct_lvalue = match self.db.lookup_intern_expr(expr) {
            Expr::Dot(expr) => self.translate_lvalue_dot(expr)?,
            Expr::Identifier(expr) => self.translate_lvalue_identifier(expr)?,
            _ => unreachable!(),
        };

        let range = self.struct_field_range(expr, field_name)?;
        Ok(struct_lvalue[range].to_vec())
    }

    fn translate_rvalue_dot(&mut self, expr: Dot) -> Result<Vec<ClifValue>> {
        let Dot { expr, field_name } = expr;
        let struct_value = self.map_expr(expr)?;
        let range = self.struct_field_range(expr, field_name)?;
        Ok(struct_value[range].to_vec())
    }

    fn translate_lvalue_identifier(&mut self, expr: Identifier) -> Result<Vec<ClifVariable>> {
        let Identifier { env, name } = expr;
        self.translate_variable(env.unwrap(), name)
    }

    fn translate_rvalue_identifier(&mut self, expr: Identifier) -> Result<Vec<ClifValue>> {
        let Identifier { env, name } = expr;
        let value = self.translate_variable(env.unwrap(), name)?;
        Ok(value.map(|variable| self.builder.use_var(variable)))
    }
}

impl<'a, 'b> ExprMap for FunctionTranslator<'a, 'b> {
    type Value = Result<Vec<ClifValue>>;

    fn lookup_expr(&self, expr: ExprId) -> Expr {
        self.db.lookup_intern_expr(expr)
    }

    fn map_arithmetic(&mut self, _expr_id: ExprId, expr: Arithmetic) -> Result<Vec<ClifValue>> {
        let Arithmetic { lhs, op, rhs } = expr;
        let lhs = self.map_expr(lhs)?.into_single_item().unwrap();
        let rhs = self.map_expr(rhs)?.into_single_item().unwrap();

        let value = match op {
            ArithmeticKind::Add => self.builder.ins().iadd(lhs, rhs),
            ArithmeticKind::Sub => self.builder.ins().isub(lhs, rhs),
            ArithmeticKind::Mul => self.builder.ins().imul(lhs, rhs),
            ArithmeticKind::Div => self.builder.ins().udiv(lhs, rhs),
        };

        Ok(vec![value])
    }

    fn map_assign(&mut self, _expr_id: ExprId, expr: Assign) -> Result<Vec<ClifValue>> {
        let Assign { lvalue, expr: assign_expr } = expr;
        let value = self.map_expr(assign_expr)?;
        let value2 = value.clone();

        match self.db.lookup_intern_expr(lvalue) {
            Expr::Deref(expr) => {
                let Deref { expr } = expr;
                let value = value.into_single_item().unwrap();
                let ptr_value = self.map_expr(expr)?.into_single_item().unwrap();
                self.builder.ins().store(MemFlags::new(), value, ptr_value, 0);
            }

            Expr::Dot(expr) => {
                let variable = self.translate_lvalue_dot(expr)?;
                assert_eq!(variable.len(), value.len());
                for (variable, value) in variable.into_iter().zip(value) {
                    self.builder.def_var(variable, value);
                }
            }

            Expr::Identifier(expr) => {
                let variable = self.translate_lvalue_identifier(expr)?;
                assert_eq!(variable.len(), value.len());
                for (variable, value) in variable.into_iter().zip(value) {
                    self.builder.def_var(variable, value);
                }
            }

            Expr::Index(expr) => {
                let Index { base, offset } = expr;
                let value = value.into_single_item().unwrap();
                let base_value = self.map_expr(base)?.into_single_item().unwrap();
                let offset_value = self.map_expr(offset)?.into_single_item().unwrap();
                let ptr_value = self.builder.ins().iadd(base_value, offset_value);
                self.builder.ins().store(MemFlags::new(), value, ptr_value, 0);
            }

            _ => unreachable!(),
        }

        Ok(value2)
    }

    fn map_block(&mut self, _expr_id: ExprId, expr: Block) -> Result<Vec<ClifValue>> {
        let Block { stmts } = expr;

        let mut value = vec![];
        for expr in stmts {
            value = self.map_expr(expr)?;
        }

        Ok(value)
    }

    fn map_call(&mut self, _expr_id: ExprId, expr: Call) -> Result<Vec<ClifValue>> {
        let Call { env, name, args } = expr;
        let (decl_env, binding) = self.db.binding_pair(self.function_name, env.unwrap(), name)?;

        let func = match binding {
            Binding::Extern(signature) => self.db.clif_func_id(true, name, signature)?,
            Binding::Function(signature) => self.db.clif_func_id(false, name, signature)?,
            Binding::Param(_) | Binding::Variable(_) => panic!("only functions can be called"),
        };

        let local_callee = {
            let Self { db, builder, clif_functions, .. } = self;
            *clif_functions
                .entry((decl_env, name))
                .or_insert_with(|| db.with_module_mut(|module| module.declare_func_in_func(func, &mut builder.func)))
        };

        let arg_values = args
            .into_iter()
            .map(|expr| self.map_expr(expr))
            .process_results(|values| values.flatten().collect::<Vec<_>>())?;

        let call = self.builder.ins().call(local_callee, &arg_values);
        Ok(self.builder.inst_results(call).to_vec())
    }

    fn map_comparison(&mut self, _expr_id: ExprId, expr: Comparison) -> Result<Vec<ClifValue>> {
        let Comparison { lhs, op, rhs } = expr;
        let lhs = self.map_expr(lhs)?.into_single_item().unwrap();
        let rhs = self.map_expr(rhs)?.into_single_item().unwrap();

        let cc = match op {
            ComparisonKind::Eq => IntCC::Equal,
            ComparisonKind::Ne => IntCC::NotEqual,
            ComparisonKind::Lt => IntCC::SignedLessThan,
            ComparisonKind::Le => IntCC::SignedLessThanOrEqual,
            ComparisonKind::Gt => IntCC::SignedGreaterThan,
            ComparisonKind::Ge => IntCC::SignedGreaterThanOrEqual,
        };

        Ok(vec![self.builder.ins().icmp(cc, lhs, rhs)])
    }

    fn map_deref(&mut self, _expr_id: ExprId, expr: Deref) -> Result<Vec<ClifValue>> {
        let Deref { expr: _expr } = expr;
        todo!()
    }

    fn map_dot(&mut self, _expr_id: ExprId, expr: Dot) -> Result<Vec<ClifValue>> {
        self.translate_rvalue_dot(expr)
    }

    fn map_global_data_addr(&mut self, expr_id: ExprId, expr: GlobalDataAddr) -> Result<Vec<ClifValue>> {
        let GlobalDataAddr { name } = expr;
        let Self { db, builder, clif_data, .. } = self;
        let data = db.clif_data_id(name)?;

        let local_id = *clif_data
            .entry(data)
            .or_insert_with(|| db.with_module_mut(|module| module.declare_data_in_func(data, &mut builder.func)));

        let ty = self.db.clif_type(self.expr_types[&expr_id])?.into_single_item().unwrap();
        Ok(vec![builder.ins().symbol_value(ty, local_id)])
    }

    fn map_identifier(&mut self, _expr_id: ExprId, expr: Identifier) -> Result<Vec<ClifValue>> {
        self.translate_rvalue_identifier(expr)
    }

    fn map_if_else(&mut self, expr_id: ExprId, expr: IfElse) -> Result<Vec<ClifValue>> {
        let IfElse { condition, then_body, else_body } = expr;
        let condition_value = self.map_expr(condition)?.into_single_item().unwrap();

        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();

        for ty in self.db.clif_type(self.expr_types[&expr_id])? {
            self.builder.append_block_param(merge_block, ty);
        }

        self.builder.ins().brz(condition_value, else_block, &[]);
        self.builder.ins().jump(then_block, &[]);

        self.builder.switch_to_block(then_block);
        self.builder.seal_block(then_block);

        let then_return = self.map_expr(then_body)?;
        self.builder.ins().jump(merge_block, &then_return);

        self.builder.switch_to_block(else_block);
        self.builder.seal_block(else_block);

        let else_return = self.map_expr(else_body)?;
        self.builder.ins().jump(merge_block, &else_return);

        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);
        Ok(self.builder.block_params(merge_block).to_vec())
    }

    fn map_index(&mut self, _expr_id: ExprId, expr: Index) -> Result<Vec<ClifValue>> {
        let Index { base: _base, offset: _offset } = expr;
        todo!()
    }

    fn map_literal(&mut self, expr_id: ExprId, expr: Literal) -> Result<Vec<ClifValue>> {
        let Literal { value } = expr;
        let ty = self.db.clif_type(self.expr_types[&expr_id])?;
        Ok(vec![self.builder.ins().iconst(ty.into_single_item().unwrap(), i64::from(value))])
    }

    fn map_scope(&mut self, _expr_id: ExprId, expr: Scope) -> Result<Vec<ClifValue>> {
        let Scope {
            scope_env,
            decl_name,
            decl_expr,
            body,
        } = expr;

        let variable = self.translate_variable(scope_env, decl_name)?;
        let value = self.map_expr(decl_expr)?;
        assert_eq!(variable.len(), value.len());
        for (variable, value) in variable.into_iter().zip(value) {
            self.builder.def_var(variable, value);
        }

        self.map_expr(body)
    }

    fn map_struct_init(&mut self, _expr_id: ExprId, expr: StructInit) -> Result<Vec<ClifValue>> {
        let StructInit { name, mut fields } = expr;
        let ty_binding = self.db.ty_binding(name)?;
        let Struct { field_names, field_tys: _ } = ty_binding.try_into().unwrap();

        let value = field_names
            .into_iter()
            .map(|field_name| {
                let field_value = fields.remove(&field_name).unwrap();
                self.map_expr(field_value)
            })
            .process_results(|values| values.flatten().collect())?;

        Ok(value)
    }

    fn map_while_loop(&mut self, _expr_id: ExprId, expr: WhileLoop) -> Result<Vec<ClifValue>> {
        let WhileLoop { condition, body } = expr;
        let header_block = self.builder.create_block();
        let body_block = self.builder.create_block();
        let exit_block = self.builder.create_block();

        self.builder.ins().jump(header_block, &[]);
        self.builder.switch_to_block(header_block);

        let condition_value = self.map_expr(condition)?.into_single_item().unwrap();
        self.builder.ins().brz(condition_value, exit_block, &[]);
        self.builder.ins().jump(body_block, &[]);

        self.builder.switch_to_block(body_block);
        self.builder.seal_block(body_block);

        self.map_expr(body)?;
        self.builder.ins().jump(header_block, &[]);

        self.builder.switch_to_block(exit_block);
        self.builder.seal_block(header_block);
        self.builder.seal_block(exit_block);
        Ok(vec![])
    }
}
