use crate::ast::expr::ExprId;
use crate::ast::{IdentId, Signature};
use derive_more::TryInto;

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Extern {
    pub signature: Signature,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Function {
    pub signature: Signature,
    pub param_names: Vec<IdentId>,
    pub body: ExprId,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, TryInto)]
#[try_into(owned, ref, ref_mut)]
pub enum Item {
    Extern(Extern),
    Function(Function),
}
