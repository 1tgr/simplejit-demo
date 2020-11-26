use crate::ast::expr::ExprId;
use crate::ast::ty::TypeId;
use crate::ast::Signature;
use derive_more::TryInto;

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Param {
    pub index: usize,
    pub ty: TypeId,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Variable {
    pub decl_expr: ExprId,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, TryInto)]
#[try_into(owned, ref, ref_mut)]
pub enum Binding {
    Extern(Signature),
    Function(Signature),
    Param(Param),
    Variable(Variable),
}
