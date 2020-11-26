use crate::ast::*;
use crate::intern::Intern;
use crate::lower::{Lower, LowerExt};
use crate::parse::ParseExt;
use crate::pretty::PrettyExt;
use crate::Result;
use std::collections::HashMap;
use std::convert::TryInto;

pub struct UnifyExprContext<'a, DB: ?Sized> {
    db: &'a DB,
    function_name: IdentId,
    result: HashMap<ExprId, TypeId>,
    ty_bindings: HashMap<i32, TypeId>,
    index: i32,
}

impl<'a, DB: Lower + ?Sized> UnifyExprContext<'a, DB> {
    pub fn new(db: &'a DB, function_name: IdentId) -> Self {
        Self {
            db,
            function_name,
            result: HashMap::new(),
            ty_bindings: HashMap::new(),
            index: 0,
        }
    }

    pub fn into_expr_type_map(self) -> HashMap<ExprId, TypeId> {
        let Self { db, mut result, ty_bindings, .. } = self;

        for (&expr, ty_mut) in result.iter_mut() {
            let ty = refine(db, &ty_bindings, *ty_mut);

            let ty = match ty {
                Type::Number => Type::Integer(Integer { signed: true, bits: 32 }),
                Type::Var(_) => panic!("didn't expect type variable to survive unification: {}", db.pretty_print_expr(self.function_name, expr)),
                _ => ty,
            };

            *ty_mut = db.intern_type(ty);
        }

        result
    }

    pub fn unify_expr(&mut self, expr: ExprId, ty: TypeId) -> Result<()> {
        let mut visitor = UnifyExprVisitor { context: self, ty };
        visitor.map_expr(expr)?;
        Ok(())
    }

    fn unify_type(&mut self, a: TypeId, b: TypeId) -> Result<TypeId> {
        let a_ty = refine(self.db, &self.ty_bindings, a);
        let b_ty = refine(self.db, &self.ty_bindings, b);
        let a = self.db.intern_type(a_ty.clone());
        let b = self.db.intern_type(b_ty.clone());
        if a == b {
            return Ok(a);
        }

        match (a_ty, b_ty) {
            (Type::Var(a), _) => {
                self.ty_bindings.insert(a, b);
                return Ok(b);
            }
            (_, Type::Var(b)) => {
                self.ty_bindings.insert(b, a);
                return Ok(a);
            }
            (Type::Pointer(a), Type::Pointer(b)) => {
                return Ok(self.db.intern_type(Type::Pointer(self.unify_type(a, b)?)));
            }
            (Type::Integer(_), Type::Number) => {
                return Ok(a);
            }
            (Type::Number, Type::Integer(_)) => {
                return Ok(b);
            }
            _ => (),
        }

        Err(error!("can't unify {} with {}", self.db.pretty_print_type(a), self.db.pretty_print_type(b)))
    }

    fn new_var(&mut self) -> TypeId {
        let ty = self.db.intern_type(Type::Var(self.index));
        self.index += 1;
        ty
    }
}

fn refine<DB: Intern + ?Sized>(db: &DB, ty_bindings: &HashMap<i32, TypeId>, ty: TypeId) -> Type {
    match db.lookup_intern_type(ty) {
        Type::Var(ty) => ty_bindings.get(&ty).map_or(Type::Var(ty), |&ty| refine(db, ty_bindings, ty)),
        ty => ty,
    }
}

struct UnifyExprVisitor<'a, 'b, DB: ?Sized> {
    context: &'a mut UnifyExprContext<'b, DB>,
    ty: TypeId,
}

impl<'a, 'b, DB: Lower + ?Sized> UnifyExprVisitor<'a, 'b, DB> {
    fn unify_type(&mut self, b: TypeId) -> Result<TypeId> {
        self.context.unify_type(self.ty, b)
    }
}

impl<'a, 'b, DB: Lower + ?Sized> ExprMap for UnifyExprVisitor<'a, 'b, DB> {
    type Value = Result<TypeId>;

    fn lookup_expr(&self, expr: ExprId) -> Expr {
        self.context.db.lookup_intern_expr(expr)
    }

    fn map_arithmetic(&mut self, _expr_id: ExprId, expr: Arithmetic) -> Result<TypeId> {
        let Arithmetic { lhs, op: _, rhs } = expr;
        let ty = self.context.db.number_type();
        self.context.unify_expr(lhs, ty)?;
        self.context.unify_expr(rhs, ty)?;
        self.unify_type(ty)
    }

    fn map_assign(&mut self, _expr_id: ExprId, expr: Assign) -> Result<TypeId> {
        let Assign { lvalue, expr } = expr;
        ensure!(matches!(self.context.db.lookup_intern_expr(lvalue), Expr::Deref(_) | Expr::Dot(_) | Expr::Identifier(_) | Expr::Index(_)));
        self.context.unify_expr(lvalue, self.ty)?;
        self.context.unify_expr(expr, self.ty)?;
        Ok(self.ty)
    }

    fn map_block(&mut self, _expr_id: ExprId, expr: Block) -> Result<TypeId> {
        let Block { stmts } = expr;
        let mut block_expr = None;
        for expr in stmts {
            let ty = self.context.new_var();
            self.context.unify_expr(expr, ty)?;
            block_expr = Some(expr);
        }

        if let Some(expr) = block_expr {
            self.context.unify_expr(expr, self.ty)?;
            Ok(self.ty)
        } else {
            self.unify_type(self.context.db.unit_type())
        }
    }

    fn map_call(&mut self, _expr_id: ExprId, expr: Call) -> Result<TypeId> {
        let Call { env, name, args } = expr;
        let binding = self.context.db.binding(self.context.function_name, env.unwrap(), name)?;
        let Signature { param_tys, return_ty } = binding.try_into().map_err(|_| error!("only functions can be called"))?;
        ensure_eq!(args.len(), param_tys.len());
        for (expr, ty) in args.into_iter().zip(param_tys) {
            self.context.unify_expr(expr, ty)?;
        }

        self.unify_type(return_ty)
    }

    fn map_comparison(&mut self, _expr_id: ExprId, expr: Comparison) -> Result<TypeId> {
        let Comparison { lhs, op: _, rhs } = expr;
        let ty = self.context.db.number_type();
        self.context.unify_expr(lhs, ty)?;
        self.context.unify_expr(rhs, ty)?;
        self.unify_type(self.context.db.bool_type())
    }

    fn map_deref(&mut self, _expr_id: ExprId, expr: Deref) -> Result<TypeId> {
        let Deref { expr } = expr;
        self.context.unify_expr(expr, self.context.db.pointer_type(self.ty))?;
        Ok(self.ty)
    }

    fn map_dot(&mut self, _expr_id: ExprId, expr: Dot) -> Self::Value {
        let Dot { expr, field_name } = expr;
        let struct_ty = self.context.new_var();
        self.context.unify_expr(expr, struct_ty)?;

        let struct_ty = refine(self.context.db, &self.context.ty_bindings, struct_ty);
        let struct_name = struct_ty.as_named().ok_or_else(|| error!("only structs can be used with ., not {:?}", struct_ty))?;
        let ty_binding = self.context.db.ty_binding(struct_name)?;
        let Struct { field_names, field_tys } = ty_binding.try_into().map_err(|e| error!("only structs can be used with ., not {}", e))?;

        let index = field_names
            .into_iter()
            .position(|n| n == field_name)
            .ok_or_else(|| error!("invalid struct field {}", self.context.db.lookup_intern_ident(field_name)))?;

        self.unify_type(field_tys[index])
    }

    fn map_global_data_addr(&mut self, _expr_id: ExprId, _expr: GlobalDataAddr) -> Result<TypeId> {
        let pointee = self.context.new_var();
        self.unify_type(self.context.db.pointer_type(pointee))
    }

    fn map_identifier(&mut self, _expr_id: ExprId, expr: Identifier) -> Result<TypeId> {
        let Identifier { env, name } = expr;
        match self.context.db.binding(self.context.function_name, env.unwrap(), name)? {
            Binding::Param(binding) => {
                let Param { index: _, ty: param_ty } = binding;
                self.unify_type(param_ty)
            }
            Binding::Variable(binding) => {
                let Variable { decl_expr } = binding;
                self.context.unify_expr(decl_expr, self.ty)?;
                Ok(self.ty)
            }
            Binding::Extern(_) | Binding::Function(_) => Err(error!("functions can only be called")),
        }
    }

    fn map_if_else(&mut self, _expr_id: ExprId, expr: IfElse) -> Result<TypeId> {
        let IfElse { condition, then_body, else_body } = expr;
        self.context.unify_expr(condition, self.context.db.bool_type())?;
        self.context.unify_expr(then_body, self.ty)?;
        self.context.unify_expr(else_body, self.ty)?;
        Ok(self.ty)
    }

    fn map_index(&mut self, _expr_id: ExprId, expr: Index) -> Result<TypeId> {
        let Index { base, offset } = expr;
        self.context.unify_expr(base, self.context.db.pointer_type(self.ty))?;
        self.context.unify_expr(offset, self.context.db.integer_type(true, 64))?;
        Ok(self.ty)
    }

    fn map_literal(&mut self, _expr_id: ExprId, _expr: Literal) -> Result<TypeId> {
        self.unify_type(self.context.db.number_type())
    }

    fn map_scope(&mut self, _expr_id: ExprId, expr: Scope) -> Result<TypeId> {
        let Scope {
            scope_env: _,
            decl_name: _,
            decl_expr: _,
            body,
        } = expr;
        self.context.unify_expr(body, self.ty)?;
        Ok(self.ty)
    }

    fn map_struct_init(&mut self, _expr_id: ExprId, expr: StructInit) -> Self::Value {
        let StructInit { name, mut fields } = expr;
        let ty_binding = self.context.db.ty_binding(name)?;
        let Struct { field_names, field_tys } = ty_binding.try_into().map_err(|e| error!("only structs can be initialized, not {}", e))?;
        for (field_name, field_ty) in field_names.into_iter().zip(field_tys) {
            let field_expr = fields.remove(&field_name).ok_or_else(|| {
                error!(
                    "missing initialization for struct field {}.{}",
                    self.context.db.lookup_intern_ident(name),
                    self.context.db.lookup_intern_ident(field_name)
                )
            })?;

            self.context.unify_expr(field_expr, field_ty)?;
        }

        self.unify_type(self.context.db.intern_type(Type::Named(name)))
    }

    fn map_while_loop(&mut self, _expr_id: ExprId, expr: WhileLoop) -> Result<TypeId> {
        let WhileLoop { condition, body } = expr;
        let body_ty = self.context.new_var();
        self.context.unify_expr(condition, self.context.db.bool_type())?;
        self.context.unify_expr(body, body_ty)?;
        self.unify_type(self.context.db.unit_type())
    }

    fn map_expr(&mut self, expr: ExprId) -> Result<TypeId> {
        let ty = self.lookup_expr(expr).map(self, expr)?;
        self.context.result.insert(expr, ty);
        Ok(ty)
    }
}
