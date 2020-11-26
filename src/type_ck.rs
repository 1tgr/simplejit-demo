use crate::ast::*;
use crate::lower::Lower;
use crate::unify::UnifyExprContext;
use crate::Result;
use std::collections::HashMap;
use std::rc::Rc;

#[salsa::query_group(TypeCkDatabase)]
pub trait TypeCk: Lower {
    fn unify_function(&self, name: IdentId) -> Result<Rc<HashMap<ExprId, TypeId>>>;
}

fn unify_function(db: &dyn TypeCk, name: IdentId) -> Result<Rc<HashMap<ExprId, TypeId>>> {
    let Signature { param_tys: _, return_ty } = db.function_signature(name)?;
    let body = db.lower_function(name)?;
    let mut context = UnifyExprContext::new(db);
    context.unify_expr(body, return_ty)?;
    Ok(Rc::new(context.into_expr_type_map()))
}
