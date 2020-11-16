use crate::ast::*;
use crate::lower::Lower;
use crate::unify::UnifyExprContext;
use crate::Result;

#[salsa::query_group(TypeCkDatabase)]
pub trait TypeCk: Lower {
    fn unify_function(&self, env: EnvId, name: IdentId) -> Result<im_rc::HashMap<ExprId, TypeId>>;
}

fn unify_function(db: &dyn TypeCk, env: EnvId, name: IdentId) -> Result<im_rc::HashMap<ExprId, TypeId>> {
    let Function { signature, param_names: _, body } = db.lower_function(env, name)?;
    let mut context = UnifyExprContext::new(db);
    context.unify_expr(body, signature.return_ty)?;
    Ok(context.to_expr_type_map())
}
