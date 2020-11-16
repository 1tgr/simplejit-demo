use crate::{Target, TargetExt};
use object_pool::Pool;
use std::rc::Rc;

#[salsa::database(
    crate::intern::InternDatabase,
    crate::jit::JITDatabase,
    crate::lower::LowerDatabase,
    crate::parse::ParseDatabase,
    crate::source::SourceDatabase,
    crate::target::TargetDatabase,
    crate::type_ck::TypeCkDatabase
)]
pub struct Database {
    storage: salsa::Storage<Database>,
}

impl salsa::Database for Database {}

impl Default for Database {
    fn default() -> Self {
        let mut db = Self {
            storage: salsa::Storage::default(),
        };

        db.reset_module();
        db.set_func_ctx_pool(Rc::new(Pool::new(0, || unreachable!())));
        db
    }
}

impl Database {
    pub fn new() -> Self {
        Self::default()
    }
}
