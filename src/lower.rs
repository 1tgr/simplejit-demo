use crate::ast::*;
use crate::intern::Intern;
use crate::{InternExt, Parse, Result};
use std::convert::Infallible;
use std::result;

#[salsa::query_group(LowerDatabase)]
pub trait Lower: Parse {
    fn lower_function(&self, name: IdentId) -> Result<Function>;
}

fn lower_function(db: &dyn Lower, name: IdentId) -> Result<Function> {
    let env = db.global_env()?;
    let Env { mut bindings } = db.lookup_intern_env(env);
    let mut function = db.function(name)?;
    for (index, (&name, &ty)) in function.param_names.iter().zip(function.signature.param_tys.iter()).enumerate() {
        bindings.insert(name, (env, Binding::Param(Param { index, ty })));
    }

    let env = db.intern_env(Env { bindings });
    function.body = LowerExprTransform { db, env }.transform_expr(function.body)?;
    Ok(function)
}

struct LowerExprTransform<'a, DB: ?Sized> {
    db: &'a DB,
    env: EnvId,
}

impl<'a, DB: Intern + ?Sized> LowerExprTransform<'a, DB> {
    fn make_scope(
        &mut self,
        mut bindings: im_rc::HashMap<IdentId, (EnvId, Binding)>,
        name: IdentId,
        decl_expr: ExprId,
        mut stmts: Vec<ExprId>,
    ) -> result::Result<Scope, Infallible> {
        let decl_expr = self.transform_expr(decl_expr)?;
        bindings.insert(name, (self.env, Binding::Variable(Variable { decl_expr })));

        let scope_env = self.db.intern_env(Env { bindings });
        let mut scope_transform = Self { db: self.db, env: scope_env };
        scope_transform.transform_stmts(&mut stmts)?;

        let body = self.intern_expr(Expr::Block(Block { stmts }));
        Ok(Scope { scope_env, name, body })
    }

    fn transform_stmts(&mut self, stmts: &mut Vec<ExprId>) -> result::Result<(), Infallible> {
        for (index, expr_mut) in stmts.iter_mut().enumerate() {
            if let Expr::Assign(assign) = self.db.lookup_intern_expr(*expr_mut) {
                let Assign { lvalue, expr: decl_expr } = assign;

                if let Expr::Identifier(lvalue) = self.db.lookup_intern_expr(lvalue) {
                    let Identifier { env: _, name } = lvalue;
                    let Env { bindings } = self.db.lookup_intern_env(self.env);

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

    fn lookup_env(&self, env: EnvId) -> Env {
        self.db.lookup_intern_env(env)
    }

    fn intern_expr(&self, expr: Expr) -> ExprId {
        if let Expr::Block(expr) = expr {
            let Block { stmts } = expr;
            self.db.intern_block(stmts)
        } else {
            self.db.intern_expr(expr)
        }
    }

    fn intern_env(&self, env: Env) -> EnvId {
        self.db.intern_env(env)
    }

    fn transform_block(&mut self, _expr_id: ExprId, mut block: Block) -> result::Result<Expr, Infallible> {
        self.transform_stmts(&mut block.stmts)?;
        Ok(Expr::Block(block))
    }

    fn transform_env(&mut self, _env: EnvId) -> result::Result<EnvId, Infallible> {
        Ok(self.env)
    }
}
