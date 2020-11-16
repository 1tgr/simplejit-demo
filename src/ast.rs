use derive_more::Display;
use derive_more::TryInto;
use im_rc::HashMap;
use salsa::InternId;

pub use crate::frontend::{ArithmeticKind, ComparisonKind};

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Display)]
#[display(fmt = "{}", "_0")]
pub struct IdentId(salsa::InternId);

impl salsa::InternKey for IdentId {
    fn from_intern_id(v: InternId) -> Self {
        Self(v)
    }

    fn as_intern_id(&self) -> InternId {
        self.0
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Display)]
#[display(fmt = "{}", "_0")]
pub struct ExprId(salsa::InternId);

impl salsa::InternKey for ExprId {
    fn from_intern_id(v: InternId) -> Self {
        Self(v)
    }

    fn as_intern_id(&self) -> InternId {
        self.0
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Display)]
#[display(fmt = "{}", "_0")]
pub struct EnvId(salsa::InternId);

impl salsa::InternKey for EnvId {
    fn from_intern_id(v: InternId) -> Self {
        Self(v)
    }

    fn as_intern_id(&self) -> InternId {
        self.0
    }
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Display)]
#[display(fmt = "{}", "_0")]
pub struct TypeId(salsa::InternId);

impl salsa::InternKey for TypeId {
    fn from_intern_id(v: InternId) -> Self {
        Self(v)
    }

    fn as_intern_id(&self) -> InternId {
        self.0
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Arithmetic {
    pub lhs: ExprId,
    pub op: ArithmeticKind,
    pub rhs: ExprId,
}

impl Arithmetic {
    pub fn walk<V: ExprVisitor + ?Sized>(self, visitor: &mut V) -> Result<(), V::Error> {
        let Self { lhs, op: _, rhs } = self;
        visitor.visit_expr(lhs)?;
        visitor.visit_expr(rhs)?;
        Ok(())
    }

    pub fn transform<T: ExprTransform + ?Sized>(mut self, transform: &mut T) -> Result<Expr, T::Error> {
        self.lhs = transform.transform_expr(self.lhs)?;
        self.rhs = transform.transform_expr(self.rhs)?;
        Ok(Expr::Arithmetic(self))
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Assign {
    pub lvalue: ExprId,
    pub expr: ExprId,
}

impl Assign {
    pub fn walk<V: ExprVisitor + ?Sized>(self, visitor: &mut V) -> Result<(), V::Error> {
        let Self { lvalue, expr } = self;
        visitor.visit_expr(lvalue)?;
        visitor.visit_expr(expr)?;
        Ok(())
    }

    pub fn transform<T: ExprTransform + ?Sized>(mut self, transform: &mut T) -> Result<Expr, T::Error> {
        self.lvalue = transform.transform_expr(self.lvalue)?;
        self.expr = transform.transform_expr(self.expr)?;
        Ok(Expr::Assign(self))
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Block {
    pub stmts: Vec<ExprId>,
}

impl Block {
    pub fn walk<V: ExprVisitor + ?Sized>(self, visitor: &mut V) -> Result<(), V::Error> {
        let Self { stmts } = self;
        for expr in stmts {
            visitor.visit_expr(expr)?;
        }

        Ok(())
    }

    pub fn transform<T: ExprTransform + ?Sized>(mut self, transform: &mut T) -> Result<Expr, T::Error> {
        for stmt in self.stmts.iter_mut() {
            *stmt = transform.transform_expr(*stmt)?;
        }

        Ok(Expr::Block(self))
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Call {
    pub env: EnvId,
    pub name: IdentId,
    pub args: Vec<ExprId>,
}

impl Call {
    pub fn walk<V: ExprVisitor + ?Sized>(self, visitor: &mut V) -> Result<(), V::Error> {
        let Self { env, name: _, args } = self;
        visitor.visit_env(env)?;

        for expr in args {
            visitor.visit_expr(expr)?;
        }

        Ok(())
    }

    pub fn transform<T: ExprTransform + ?Sized>(mut self, transform: &mut T) -> Result<Expr, T::Error> {
        self.env = transform.transform_env(self.env)?;

        for expr in self.args.iter_mut() {
            *expr = transform.transform_expr(*expr)?;
        }

        Ok(Expr::Call(self))
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Comparison {
    pub lhs: ExprId,
    pub op: ComparisonKind,
    pub rhs: ExprId,
}

impl Comparison {
    pub fn walk<V: ExprVisitor + ?Sized>(self, visitor: &mut V) -> Result<(), V::Error> {
        let Self { lhs, op: _, rhs } = self;
        visitor.visit_expr(lhs)?;
        visitor.visit_expr(rhs)?;
        Ok(())
    }

    pub fn transform<T: ExprTransform + ?Sized>(mut self, transform: &mut T) -> Result<Expr, T::Error> {
        self.lhs = transform.transform_expr(self.lhs)?;
        self.rhs = transform.transform_expr(self.rhs)?;
        Ok(Expr::Comparison(self))
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Deref {
    pub expr: ExprId,
}

impl Deref {
    pub fn walk<V: ExprVisitor + ?Sized>(self, visitor: &mut V) -> Result<(), V::Error> {
        let Self { expr } = self;
        visitor.visit_expr(expr)?;
        Ok(())
    }

    pub fn transform<T: ExprTransform + ?Sized>(mut self, transform: &mut T) -> Result<Expr, T::Error> {
        self.expr = transform.transform_expr(self.expr)?;
        Ok(Expr::Deref(self))
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct GlobalDataAddr {
    pub name: IdentId,
}

impl GlobalDataAddr {
    pub fn walk<V: ExprVisitor + ?Sized>(self, _visitor: &mut V) -> Result<(), V::Error> {
        let Self { name: _name } = self;
        Ok(())
    }

    pub fn transform<T: ExprTransform + ?Sized>(self, _transform: &mut T) -> Result<Expr, T::Error> {
        Ok(Expr::GlobalDataAddr(self))
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Identifier {
    pub env: EnvId,
    pub name: IdentId,
}

impl Identifier {
    pub fn walk<V: ExprVisitor + ?Sized>(self, visitor: &mut V) -> Result<(), V::Error> {
        let Self { env, name: _name } = self;
        visitor.visit_env(env)?;
        Ok(())
    }

    pub fn transform<T: ExprTransform + ?Sized>(mut self, transform: &mut T) -> Result<Expr, T::Error> {
        self.env = transform.transform_env(self.env)?;
        Ok(Expr::Identifier(self))
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct IfElse {
    pub condition: ExprId,
    pub then_body: ExprId,
    pub else_body: ExprId,
}

impl IfElse {
    pub fn walk<V: ExprVisitor + ?Sized>(self, visitor: &mut V) -> Result<(), V::Error> {
        let Self { condition, then_body, else_body } = self;
        visitor.visit_expr(condition)?;
        visitor.visit_expr(then_body)?;
        visitor.visit_expr(else_body)?;
        Ok(())
    }

    pub fn transform<T: ExprTransform + ?Sized>(mut self, transform: &mut T) -> Result<Expr, T::Error> {
        self.condition = transform.transform_expr(self.condition)?;
        self.then_body = transform.transform_expr(self.then_body)?;
        self.else_body = transform.transform_expr(self.else_body)?;
        Ok(Expr::IfElse(self))
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Index {
    pub base: ExprId,
    pub offset: ExprId,
}

impl Index {
    pub fn walk<V: ExprVisitor + ?Sized>(self, visitor: &mut V) -> Result<(), V::Error> {
        let Self { base, offset } = self;
        visitor.visit_expr(base)?;
        visitor.visit_expr(offset)?;
        Ok(())
    }

    pub fn transform<T: ExprTransform + ?Sized>(mut self, transform: &mut T) -> Result<Expr, T::Error> {
        self.base = transform.transform_expr(self.base)?;
        self.offset = transform.transform_expr(self.offset)?;
        Ok(Expr::Index(self))
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Literal {
    pub value: i32,
}

impl Literal {
    pub fn walk<V: ExprVisitor + ?Sized>(self, _visitor: &mut V) -> Result<(), V::Error> {
        let Self { value: _value } = self;
        Ok(())
    }

    pub fn transform<T: ExprTransform + ?Sized>(self, _transform: &mut T) -> Result<Expr, T::Error> {
        Ok(Expr::Literal(self))
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Scope {
    pub scope_env: EnvId,
    pub name: IdentId,
    pub body: ExprId,
}

impl Scope {
    pub fn walk<V: ExprVisitor + ?Sized>(self, visitor: &mut V) -> Result<(), V::Error> {
        let Self { scope_env, name, body } = self;
        visitor.visit_env(scope_env)?;

        let Env { bindings } = visitor.lookup_env(scope_env);
        if let (_, Binding::Variable(binding)) = &bindings[&name] {
            let &Variable { decl_expr } = binding;
            visitor.visit_expr(decl_expr)?;
        }

        visitor.visit_expr(body)?;
        Ok(())
    }

    pub fn transform<T: ExprTransform + ?Sized>(mut self, transform: &mut T) -> Result<Expr, T::Error> {
        self.scope_env = transform.transform_env(self.scope_env)?;

        let Env { mut bindings } = transform.lookup_env(self.scope_env);
        if let (_, Binding::Variable(binding)) = &mut bindings[&self.name] {
            binding.decl_expr = transform.transform_expr(binding.decl_expr)?;
            self.scope_env = transform.intern_env(Env { bindings });
        }

        self.body = transform.transform_expr(self.body)?;
        Ok(Expr::Scope(self))
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct WhileLoop {
    pub condition: ExprId,
    pub body: ExprId,
}

impl WhileLoop {
    pub fn walk<V: ExprVisitor + ?Sized>(self, visitor: &mut V) -> Result<(), V::Error> {
        let Self { condition, body } = self;
        visitor.visit_expr(condition)?;
        visitor.visit_expr(body)?;
        Ok(())
    }

    pub fn transform<T: ExprTransform + ?Sized>(mut self, transform: &mut T) -> Result<Expr, T::Error> {
        self.condition = transform.transform_expr(self.condition)?;
        self.body = transform.transform_expr(self.body)?;
        Ok(Expr::WhileLoop(self))
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Function {
    pub signature: Signature,
    pub param_names: Vec<IdentId>,
    pub body: ExprId,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Signature {
    pub param_tys: Vec<TypeId>,
    pub return_ty: TypeId,
}

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

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Env {
    pub bindings: HashMap<IdentId, (EnvId, Binding)>,
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
    Number,
    Pointer(TypeId),
    Unit,
    Var(i32),
}

macro_rules! expr_enum {
    ( $( [ $ty:ident, $visit:ident, $transform:ident, $map:ident ] ),* ) => {
        #[derive(Clone, Debug, Hash, PartialEq, Eq, TryInto)]
        #[try_into(owned, ref, ref_mut)]
        pub enum Expr {
            $(
                $ty($ty),
            )*
        }

        impl Expr {
            pub fn walk<V: ExprVisitor + ?Sized>(self, expr_id: ExprId, visitor: &mut V) -> Result<(), V::Error> {
                match self {
                    $(
                        Self::$ty(expr) => visitor.$visit(expr_id, expr),
                    )*
                }
            }

            pub fn transform<T: ExprTransform + ?Sized>(self, expr_id: ExprId, transform: &mut T) -> Result<Self, T::Error> {
                match self {
                    $(
                        Self::$ty(expr) => transform.$transform(expr_id, expr),
                    )*
                }
            }

            pub fn map<M: ExprMap + ?Sized>(self, map: &mut M, expr_id: ExprId) -> M::Value {
                match self {
                    $(
                        Self::$ty(expr) => map.$map(expr_id, expr),
                    )*
                }
            }
        }

        pub trait ExprVisitor {
            type Error;

            fn lookup_expr(&self, expr: ExprId) -> Expr;
            fn lookup_env(&self, env: EnvId) -> Env;

            $(
                #[allow(unused_variables)]
                fn $visit(&mut self, expr_id: ExprId, expr: $ty) -> Result<(), Self::Error> {
                    expr.walk(self)
                }
            )*

            fn visit_expr(&mut self, expr: ExprId) -> Result<(), Self::Error> {
                self.lookup_expr(expr).walk(expr, self)
            }

            #[allow(unused_variables)]
            fn visit_env(&mut self, env: EnvId) -> Result<(), Self::Error> {
                Ok(())
            }
        }

        pub trait ExprTransform {
            type Error;

            fn lookup_expr(&self, expr: ExprId) -> Expr;
            fn lookup_env(&self, env: EnvId) -> Env;

            fn intern_expr(&self, expr: Expr) -> ExprId;
            fn intern_env(&self, env: Env) -> EnvId;

            $(
                #[allow(unused_variables)]
                fn $transform(&mut self, expr_id: ExprId, expr: $ty) -> Result<Expr, Self::Error> {
                    expr.transform(self)
                }
            )*

            fn transform_expr(&mut self, expr: ExprId) -> Result<ExprId, Self::Error> {
                self.lookup_expr(expr).transform(expr, self).map(|expr| self.intern_expr(expr))
            }

            fn transform_env(&mut self, env: EnvId) -> Result<EnvId, Self::Error> {
                Ok(env)
            }
        }

        pub trait ExprMap {
            type Value;

            fn lookup_expr(&self, expr: ExprId) -> Expr;

            $(
                fn $map(&mut self, expr_id: ExprId, expr: $ty) -> Self::Value;
            )*

            fn map_expr(&mut self, expr: ExprId) -> Self::Value {
                self.lookup_expr(expr).map(self, expr)
            }
        }
    };
}

expr_enum! {
    [ Arithmetic, visit_arithmetic, transform_arithmetic, map_arithmetic ],
    [ Assign, visit_assign, transform_assign, map_assign ],
    [ Block, visit_block, transform_block, map_block ],
    [ Call, visit_call, transform_call, map_call ],
    [ Comparison, visit_comparison, transform_comparison, map_comparison ],
    [ Deref, visit_deref, transform_deref, map_deref ],
    [ GlobalDataAddr, visit_global_data_addr, transform_global_data_addr, map_global_data_addr ],
    [ Identifier, visit_identifier, transform_identifier, map_identifier ],
    [ IfElse, visit_if_else, transform_if_else, map_if_else ],
    [ Index, visit_index, transform_index, map_index ],
    [ Literal, visit_literal, transform_literal, map_literal ],
    [ Scope, visit_scope, transform_scope, map_scope ],
    [ WhileLoop, visit_while_loop, transform_while_loop, map_while_loop ]
}
