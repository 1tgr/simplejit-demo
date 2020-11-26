use crate::ast::*;
use crate::intern::Intern;
use crate::{InternExt, Parse, Result};
use std::collections::HashMap;
use std::convert::Infallible;
use std::num::NonZeroU32;
use std::rc::Rc;
use std::result;

#[salsa::query_group(LowerDatabase)]
pub trait Lower: Parse {
    fn lower_function(&self, name: IdentId) -> Result<(Rc<HashMap<EnvId, Env>>, ExprId)>;
}

fn lower_function(db: &dyn Lower, name: IdentId) -> Result<(Rc<HashMap<EnvId, Env>>, ExprId)> {
    let mut index = 2;
    let mut envs = HashMap::new();
    let env = EnvId::from(NonZeroU32::new(index).unwrap());
    index += 1;

    let Env { mut bindings } = db.global_env()?;
    let Function { signature, param_names, body } = db.function(name)?;
    let Signature { param_tys, return_ty: _ } = signature;
    for (index, (name, ty)) in param_names.into_iter().zip(param_tys).enumerate() {
        bindings.insert(name, (env, Binding::Param(Param { index, ty })));
    }

    envs.insert(env, Env { bindings });

    let body = LowerExprTransform {
        db,
        env,
        envs: &mut envs,
        index: &mut index,
    }
    .transform_expr(body)?;

    Ok((Rc::new(envs), body))
}

pub trait LowerExt: Lower {
    fn binding(&self, function_name: IdentId, env: EnvId, name: IdentId) -> Result<(EnvId, Binding)> {
        let (envs, _) = self.lower_function(function_name)?;
        let Env { bindings } = &envs[&env];
        let binding = bindings
            .get(&name)
            .ok_or_else(|| error!("reading from undeclared variable {}", self.lookup_intern_ident(name)))?;

        Ok(binding.clone())
    }
}

impl<T: Lower + ?Sized> LowerExt for T {}

struct LowerExprTransform<'a, DB: ?Sized> {
    db: &'a DB,
    env: EnvId,
    envs: &'a mut HashMap<EnvId, Env>,
    index: &'a mut u32,
}

impl<'a, DB: Intern + ?Sized> LowerExprTransform<'a, DB> {
    fn make_scope(
        &mut self,
        mut bindings: im_rc::HashMap<IdentId, (EnvId, Binding)>,
        decl_name: IdentId,
        decl_expr: ExprId,
        mut stmts: Vec<ExprId>,
    ) -> result::Result<Scope, Infallible> {
        let scope_env = EnvId::from(NonZeroU32::new(*self.index).unwrap());
        *self.index += 1;

        let decl_expr = self.transform_expr(decl_expr)?;
        bindings.insert(decl_name, (scope_env, Binding::Variable(Variable { decl_expr })));
        self.envs.insert(scope_env, Env { bindings });

        LowerExprTransform {
            db: self.db,
            env: scope_env,
            envs: self.envs,
            index: self.index,
        }
        .transform_stmts(&mut stmts)?;

        let body = self.db.intern_block(stmts);

        Ok(Scope {
            scope_env,
            decl_name,
            decl_expr,
            body,
        })
    }

    fn transform_stmts(&mut self, stmts: &mut Vec<ExprId>) -> result::Result<(), Infallible> {
        for (index, expr_mut) in stmts.iter_mut().enumerate() {
            if let Expr::Assign(assign) = self.db.lookup_intern_expr(*expr_mut) {
                let Assign { lvalue, expr: decl_expr } = assign;

                if let Expr::Identifier(lvalue) = self.db.lookup_intern_expr(lvalue) {
                    let Identifier { env: _, name } = lvalue;
                    let Env { bindings } = self.envs[&self.env].clone();

                    if !bindings.contains_key(&name) {
                        let body = stmts.split_off(index + 1);
                        let scope = self.make_scope(bindings, name, decl_expr, body)?;
                        stmts[index] = self.intern_expr(Expr::Scope(scope));
                        return Ok(());
                    }
                }
            }

            *expr_mut = self.transform_expr(*expr_mut)?;
        }

        Ok(())
    }
}

impl<'a, DB: Intern + InternExt + ?Sized> ExprTransform for LowerExprTransform<'a, DB> {
    type Error = Infallible;

    fn lookup_expr(&self, expr: ExprId) -> Expr {
        self.db.lookup_intern_expr(expr)
    }

    fn intern_expr(&self, expr: Expr) -> ExprId {
        if let Expr::Block(expr) = expr {
            let Block { stmts } = expr;
            self.db.intern_block(stmts)
        } else {
            self.db.intern_expr(expr)
        }
    }

    fn transform_block(&mut self, _expr_id: ExprId, mut expr: Block) -> result::Result<Expr, Infallible> {
        self.transform_stmts(&mut expr.stmts)?;
        Ok(Expr::Block(expr))
    }

    fn transform_call(&mut self, _expr_id: ExprId, mut expr: Call) -> result::Result<Expr, Infallible> {
        expr.env = Some(self.env);
        expr.transform(self)
    }

    fn transform_identifier(&mut self, _expr_id: ExprId, mut expr: Identifier) -> result::Result<Expr, Infallible> {
        expr.env = Some(self.env);
        expr.transform(self)
    }
}
