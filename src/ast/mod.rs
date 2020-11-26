use derive_more::{Display, From, Into};
use im_rc::HashMap;
use std::num::NonZeroU32;

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Display)]
#[display(fmt = "{}", "_0")]
pub struct IdentId(salsa::InternId);

impl salsa::InternKey for IdentId {
    fn from_intern_id(v: salsa::InternId) -> Self {
        Self(v)
    }

    fn as_intern_id(&self) -> salsa::InternId {
        self.0
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Display, From, Into)]
#[display(fmt = "{}", "_0")]
pub struct EnvId(NonZeroU32);

impl EnvId {
    pub const GLOBAL: Self = Self(unsafe { NonZeroU32::new_unchecked(1) });
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Signature {
    pub param_tys: Vec<TypeId>,
    pub return_ty: TypeId,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Env {
    pub bindings: HashMap<IdentId, (EnvId, Binding)>,
}

mod binding;
mod expr;
mod item;
mod ty;

pub use crate::frontend::{ArithmeticKind, ComparisonKind};
pub use binding::*;
pub use expr::*;
pub use item::*;
pub use ty::*;
