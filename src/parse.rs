use crate::ast::*;
use crate::frontend::parser;
use crate::intern::{Intern, InternExt};
use crate::source::Source;
use crate::Result;
use std::collections::HashMap;
use std::convert::TryInto;
use std::rc::Rc;

#[salsa::query_group(ParseDatabase)]
pub trait Parse: Source + Intern {
    fn module(&self) -> Result<Rc<HashMap<IdentId, Item>>>;
    fn functions(&self) -> Result<Rc<HashMap<IdentId, Function>>>;
    fn function_names(&self) -> Result<Vec<IdentId>>;
    fn function(&self, name: IdentId) -> Result<Function>;
    fn function_body(&self, name: IdentId) -> Result<ExprId>;
    fn function_signature(&self, name: IdentId) -> Result<Signature>;
    fn global_env(&self) -> Result<Env>;
}

fn module(db: &dyn Parse) -> Result<Rc<HashMap<IdentId, Item>>> {
    let input = db.source();
    let items = parser::module(&input)?;

    let items = items
        .into_iter()
        .map(|(name, i)| {
            let name = db.intern_ident(name);
            let i = db.intern_frontend_item(i);
            (name, i)
        })
        .collect();

    Ok(Rc::new(items))
}

fn functions(db: &dyn Parse) -> Result<Rc<HashMap<IdentId, Function>>> {
    let items = db.module()?;

    let functions = items
        .iter()
        .filter_map(|(&name, item)| {
            let item = item.try_into().ok()?;
            Some((name, Function::clone(item)))
        })
        .collect();

    Ok(Rc::new(functions))
}

fn function_names(db: &dyn Parse) -> Result<Vec<IdentId>> {
    let functions = db.functions()?;
    let mut names = functions.keys().copied().collect::<Vec<_>>();
    names.sort_by_key(|&name| db.lookup_intern_ident(name));
    Ok(names)
}

fn function(db: &dyn Parse, name: IdentId) -> Result<Function> {
    let functions = db.functions()?;
    let function = functions.get(&name).ok_or_else(|| error!("undefined function {}", db.lookup_intern_ident(name)))?;
    Ok(function.clone())
}

fn function_body(db: &dyn Parse, name: IdentId) -> Result<ExprId> {
    let Function {
        signature: _,
        param_names: _,
        body,
    } = db.function(name)?;

    Ok(body)
}

fn function_signature(db: &dyn Parse, name: IdentId) -> Result<Signature> {
    let Function {
        signature,
        param_names: _,
        body: _,
    } = db.function(name)?;

    Ok(signature)
}

fn global_env(db: &dyn Parse) -> Result<Env> {
    let mut bindings = im_rc::HashMap::new();
    let mut ty_bindings = im_rc::HashMap::new();

    for (&name, item) in db.module()?.iter() {
        match item.clone() {
            Item::Extern(item) => {
                let Extern { signature } = item;
                bindings.insert(name, (EnvId::GLOBAL, Binding::Extern(signature)));
            }

            Item::Function(item) => {
                let Function {
                    signature,
                    param_names: _,
                    body: _,
                } = item;

                bindings.insert(name, (EnvId::GLOBAL, Binding::Function(signature)));
            }

            Item::Struct(item) => {
                ty_bindings.insert(name, TyBinding::Struct(item));
            }
        }
    }

    Ok(Env { bindings, ty_bindings })
}

pub trait ParseExt: Parse {
    fn ty_binding(&self, name: IdentId) -> Result<TyBinding> {
        let Env { bindings: _, ty_bindings } = self.global_env()?;
        let ty_binding = ty_bindings.get(&name).ok_or_else(|| error!("using undeclared type {}", self.lookup_intern_ident(name)))?;
        Ok(ty_binding.clone())
    }
}

impl<T: Parse + ?Sized> ParseExt for T {}
