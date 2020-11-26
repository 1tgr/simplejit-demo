use crate::ast::item::Struct;
use derive_more::TryInto;

#[derive(Clone, Debug, Hash, PartialEq, Eq, TryInto)]
#[try_into(owned, ref, ref_mut)]
pub enum TyBinding {
    Struct(Struct),
}
