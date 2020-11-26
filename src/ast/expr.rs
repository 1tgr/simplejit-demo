use crate::ast::{ArithmeticKind, ComparisonKind, EnvId, IdentId};
use derive_more::{Display, TryInto};

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq, Display)]
#[display(fmt = "{}", "_0")]
pub struct ExprId(salsa::InternId);

impl salsa::InternKey for ExprId {
    fn from_intern_id(v: salsa::InternId) -> Self {
        Self(v)
    }

    fn as_intern_id(&self) -> salsa::InternId {
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
    pub env: Option<EnvId>,
    pub name: IdentId,
    pub args: Vec<ExprId>,
}

impl Call {
    pub fn walk<V: ExprVisitor + ?Sized>(self, visitor: &mut V) -> Result<(), V::Error> {
        let Self { env: _, name: _, args } = self;
        for expr in args {
            visitor.visit_expr(expr)?;
        }

        Ok(())
    }

    pub fn transform<T: ExprTransform + ?Sized>(mut self, transform: &mut T) -> Result<Expr, T::Error> {
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
pub struct Dot {
    pub expr: ExprId,
    pub field_name: IdentId,
}

impl Dot {
    pub fn walk<V: ExprVisitor + ?Sized>(self, visitor: &mut V) -> Result<(), V::Error> {
        let Self { expr, field_name: _ } = self;
        visitor.visit_expr(expr)?;
        Ok(())
    }

    pub fn transform<T: ExprTransform + ?Sized>(mut self, transform: &mut T) -> Result<Expr, T::Error> {
        self.expr = transform.transform_expr(self.expr)?;
        Ok(Expr::Dot(self))
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
    pub env: Option<EnvId>,
    pub name: IdentId,
}

impl Identifier {
    pub fn walk<V: ExprVisitor + ?Sized>(self, _visitor: &mut V) -> Result<(), V::Error> {
        Ok(())
    }

    pub fn transform<T: ExprTransform + ?Sized>(self, _transform: &mut T) -> Result<Expr, T::Error> {
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
    pub decl_name: IdentId,
    pub decl_expr: ExprId,
    pub body: ExprId,
}

impl Scope {
    pub fn walk<V: ExprVisitor + ?Sized>(self, visitor: &mut V) -> Result<(), V::Error> {
        let Self {
            scope_env: _,
            decl_name: _,
            decl_expr,
            body,
        } = self;
        visitor.visit_expr(decl_expr)?;
        visitor.visit_expr(body)?;
        Ok(())
    }

    pub fn transform<T: ExprTransform + ?Sized>(mut self, transform: &mut T) -> Result<Expr, T::Error> {
        self.decl_expr = transform.transform_expr(self.decl_expr)?;
        self.body = transform.transform_expr(self.body)?;
        Ok(Expr::Scope(self))
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct StructInit {
    pub name: IdentId,
    pub fields: im_rc::HashMap<IdentId, ExprId>,
}

impl StructInit {
    pub fn walk<V: ExprVisitor + ?Sized>(self, visitor: &mut V) -> Result<(), V::Error> {
        let Self { name: _, fields } = self;
        for &expr in fields.values() {
            visitor.visit_expr(expr)?;
        }

        Ok(())
    }

    pub fn transform<T: ExprTransform + ?Sized>(mut self, transform: &mut T) -> Result<Expr, T::Error> {
        for (_, expr_mut) in self.fields.iter_mut() {
            *expr_mut = transform.transform_expr(*expr_mut)?;
        }

        Ok(Expr::StructInit(self))
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

            $(
                #[allow(unused_variables)]
                fn $visit(&mut self, expr_id: ExprId, expr: $ty) -> Result<(), Self::Error> {
                    expr.walk(self)
                }
            )*

            fn visit_expr(&mut self, expr: ExprId) -> Result<(), Self::Error> {
                self.lookup_expr(expr).walk(expr, self)
            }
        }

        pub trait ExprTransform {
            type Error;

            fn lookup_expr(&self, expr: ExprId) -> Expr;

            fn intern_expr(&self, expr: Expr) -> ExprId;

            $(
                #[allow(unused_variables)]
                fn $transform(&mut self, expr_id: ExprId, expr: $ty) -> Result<Expr, Self::Error> {
                    expr.transform(self)
                }
            )*

            fn transform_expr(&mut self, expr: ExprId) -> Result<ExprId, Self::Error> {
                self.lookup_expr(expr).transform(expr, self).map(|expr| self.intern_expr(expr))
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
    [ Dot, visit_dot, transform_dot, map_dot ],
    [ GlobalDataAddr, visit_global_data_addr, transform_global_data_addr, map_global_data_addr ],
    [ Identifier, visit_identifier, transform_identifier, map_identifier ],
    [ IfElse, visit_if_else, transform_if_else, map_if_else ],
    [ Index, visit_index, transform_index, map_index ],
    [ Literal, visit_literal, transform_literal, map_literal ],
    [ Scope, visit_scope, transform_scope, map_scope ],
    [ StructInit, visit_struct_init, transform_struct_init, map_struct_init ],
    [ WhileLoop, visit_while_loop, transform_while_loop, map_while_loop ]
}
