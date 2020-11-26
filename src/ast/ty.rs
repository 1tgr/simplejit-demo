use crate::ast::IdentId;
use derive_more::Display;

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Display)]
#[display(fmt = "{}", "_0")]
pub struct TypeId(salsa::InternId);

impl salsa::InternKey for TypeId {
    fn from_intern_id(v: salsa::InternId) -> Self {
        Self(v)
    }

    fn as_intern_id(&self) -> salsa::InternId {
        self.0
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Integer {
    pub signed: bool,
    pub bits: u16,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Type {
    Bool,
    Integer(Integer),
    Named(IdentId),
    Number,
    Pointer(TypeId),
    Unit,
    Var(i32),
}

impl Type {
    pub fn as_named(&self) -> Option<IdentId> {
        if let &Self::Named(ty) = self {
            Some(ty)
        } else {
            None
        }
    }
}
