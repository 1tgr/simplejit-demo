use crate::ast::{Binding, Env, EnvId, Function, IdentId, Signature};
use crate::frontend::parser;
use crate::intern::{Intern, InternExt};
use crate::source::Source;
use crate::Result;
use std::collections::HashMap;

#[salsa::query_group(ParseDatabase)]
pub trait Parse: Source + Intern {
    fn module(&self) -> Result<HashMap<IdentId, (Function, Vec<IdentId>)>>;
    fn function_names(&self) -> Result<Vec<IdentId>>;
    fn function(&self, name: IdentId) -> Result<(Function, Vec<IdentId>)>;
    fn function_signature(&self, name: IdentId) -> Result<Signature>;
    fn function_param_names(&self, name: IdentId) -> Result<Vec<IdentId>>;
    fn global_env(&self) -> Result<EnvId>;
}

fn module(db: &dyn Parse) -> Result<HashMap<IdentId, (Function, Vec<IdentId>)>> {
    let input = db.source();
    let functions = parser::module(&input)?;

    let functions = functions
        .into_iter()
        .map(|(name, f)| {
            let name = db.intern_ident(name);
            let f = db.intern_frontend_function(f);
            (name, f)
        })
        .collect();

    Ok(functions)
}

fn function_names(db: &dyn Parse) -> Result<Vec<IdentId>> {
    let module = db.module()?;
    let mut names = module.keys().copied().collect::<Vec<_>>();
    names.sort_by_key(|&name| db.lookup_intern_ident(name));
    Ok(names)
}

fn function(db: &dyn Parse, name: IdentId) -> Result<(Function, Vec<IdentId>)> {
    let mut module = db.module()?;
    module.remove(&name).ok_or_else(|| error!("undefined function {}", db.lookup_intern_ident(name)))
}

fn function_signature(db: &dyn Parse, name: IdentId) -> Result<Signature> {
    let (function, _) = db.function(name)?;
    Ok(function.signature)
}

fn function_param_names(db: &dyn Parse, name: IdentId) -> Result<Vec<IdentId>> {
    let (_, param_names) = db.function(name)?;
    Ok(param_names)
}

fn global_env(db: &dyn Parse) -> Result<EnvId> {
    let decl_env = db.empty_env();
    let mut bindings = im_rc::HashMap::new();
    for name in db.function_names()? {
        bindings.insert(name, (decl_env, Binding::Function(db.function_signature(name)?)));
    }

    bindings.insert(
        db.intern_ident("free".to_owned()),
        (
            decl_env,
            Binding::Extern(Signature {
                param_tys: vec![db.pointer_type(db.integer_type(false, 8))],
                return_ty: db.unit_type(),
            }),
        ),
    );

    bindings.insert(
        db.intern_ident("puts".to_owned()),
        (
            decl_env,
            Binding::Extern(Signature {
                param_tys: vec![db.pointer_type(db.integer_type(false, 8))],
                return_ty: db.integer_type(true, 32),
            }),
        ),
    );

    bindings.insert(
        db.intern_ident("strdup".to_owned()),
        (
            decl_env,
            Binding::Extern(Signature {
                param_tys: vec![db.pointer_type(db.integer_type(false, 8))],
                return_ty: db.pointer_type(db.integer_type(false, 8)),
            }),
        ),
    );

    Ok(db.intern_env(Env { bindings }))
}
