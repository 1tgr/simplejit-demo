use crate::ast::*;
use crate::{frontend, VecExt, VecMapExt};

#[salsa::query_group(InternDatabase)]
pub trait Intern {
    #[salsa::interned]
    fn intern_ident(&self, ident: String) -> IdentId;

    #[salsa::interned]
    fn intern_expr(&self, expr: Expr) -> ExprId;

    #[salsa::interned]
    fn intern_type(&self, ty: Type) -> TypeId;

    fn bool_type(&self) -> TypeId;
    fn integer_type(&self, signed: bool, bits: u16) -> TypeId;
    fn number_type(&self) -> TypeId;
    fn pointer_type(&self, pointee: TypeId) -> TypeId;
    fn unit_type(&self) -> TypeId;
}

fn bool_type(db: &dyn Intern) -> TypeId {
    db.intern_type(Type::Bool)
}

fn integer_type(db: &dyn Intern, signed: bool, bits: u16) -> TypeId {
    db.intern_type(Type::Integer(Integer { signed, bits }))
}

fn number_type(db: &dyn Intern) -> TypeId {
    db.intern_type(Type::Number)
}

fn pointer_type(db: &dyn Intern, pointee: TypeId) -> TypeId {
    db.intern_type(Type::Pointer(pointee))
}

fn unit_type(db: &dyn Intern) -> TypeId {
    db.intern_type(Type::Unit)
}

pub trait InternExt: Intern {
    fn intern_frontend_expr(&self, expr: frontend::Expr) -> ExprId {
        use frontend::Expr as E;

        let expr = match expr {
            E::Arithmetic(lhs, op, rhs) => {
                let lhs = self.intern_frontend_expr(*lhs);
                let rhs = self.intern_frontend_expr(*rhs);
                Expr::Arithmetic(Arithmetic { lhs, op, rhs })
            }

            E::Assign(lvalue, expr) => {
                let lvalue = self.intern_frontend_expr(*lvalue);
                let expr = self.intern_frontend_expr(*expr);
                Expr::Assign(Assign { lvalue, expr })
            }

            E::Call(name, args) => {
                let name = self.intern_ident(name);
                let args = args.into_iter().map(|expr| self.intern_frontend_expr(expr)).collect();
                Expr::Call(Call { env: None, name, args })
            }

            E::Comparison(lhs, op, rhs) => {
                let lhs = self.intern_frontend_expr(*lhs);
                let rhs = self.intern_frontend_expr(*rhs);
                Expr::Comparison(Comparison { lhs, op, rhs })
            }

            E::Deref(expr) => {
                let expr = self.intern_frontend_expr(*expr);
                Expr::Deref(Deref { expr })
            }

            E::Dot(expr, name) => {
                let expr = self.intern_frontend_expr(*expr);
                let name = self.intern_ident(name);
                Expr::Dot(Dot { expr, field_name: name })
            }

            E::GlobalDataAddr(name) => {
                let name = self.intern_ident(name);
                Expr::GlobalDataAddr(GlobalDataAddr { name })
            }

            E::Identifier(name) => {
                let name = self.intern_ident(name);
                Expr::Identifier(Identifier { env: None, name })
            }

            E::IfElse(condition, then_stmts, else_stmts) => {
                let condition = self.intern_frontend_expr(*condition);
                let then_body = self.intern_frontend_block(then_stmts);
                let else_body = self.intern_frontend_block(else_stmts);
                Expr::IfElse(IfElse { condition, then_body, else_body })
            }

            E::Index(base, offset) => {
                let base = self.intern_frontend_expr(*base);
                let offset = self.intern_frontend_expr(*offset);
                Expr::Index(Index { base, offset })
            }

            E::Literal(value) => Expr::Literal(Literal { value }),

            E::StructInit(name, fields) => {
                let name = self.intern_ident(name);
                let fields = fields.into_iter().map(|(name, expr)| (self.intern_ident(name), self.intern_frontend_expr(*expr))).collect();
                Expr::StructInit(StructInit { name, fields })
            }

            E::WhileLoop(condition, stmts) => {
                let condition = self.intern_frontend_expr(*condition);
                let body = self.intern_frontend_block(stmts);
                Expr::WhileLoop(WhileLoop { condition, body })
            }
        };

        self.intern_expr(expr)
    }

    fn intern_frontend_type(&self, ty: frontend::Type) -> TypeId {
        use frontend::Type as T;

        let ty = match ty {
            T::I32 => Type::Integer(Integer { signed: true, bits: 32 }),
            T::Named(name) => Type::Named(self.intern_ident(name)),
            T::Pointer(ty) => Type::Pointer(self.intern_frontend_type(*ty)),
            T::U8 => Type::Integer(Integer { signed: false, bits: 8 }),
            T::Unit => Type::Unit,
        };

        self.intern_type(ty)
    }

    fn intern_frontend_block(&self, stmts: Vec<frontend::Expr>) -> ExprId {
        let stmts = stmts.map(|expr| self.intern_frontend_expr(expr));
        self.intern_block(stmts)
    }

    fn intern_frontend_item(&self, item: frontend::Item) -> Item {
        use frontend::Item as I;

        match item {
            I::Extern(item) => {
                let frontend::Extern { params, return_ty } = item;
                let param_tys = params.into_iter().map(|(_, ty)| self.intern_frontend_type(ty)).collect();
                let return_ty = self.intern_frontend_type(return_ty);
                let signature = Signature { param_tys, return_ty };
                Item::Extern(Extern { signature })
            }

            I::Function(item) => {
                let frontend::Function { params, return_ty, stmts } = item;
                let (param_names, param_tys) = params.into_iter().map(|(name, ty)| (self.intern_ident(name), self.intern_frontend_type(ty))).unzip();
                let return_ty = self.intern_frontend_type(return_ty);
                let body = self.intern_frontend_block(stmts);
                let signature = Signature { param_tys, return_ty };
                Item::Function(Function { signature, param_names, body })
            }

            I::Struct(item) => {
                let frontend::Struct { fields } = item;
                let (field_names, field_tys) = fields.into_iter().map(|(name, ty)| (self.intern_ident(name), self.intern_frontend_type(ty))).unzip();
                Item::Struct(Struct { field_names, field_tys })
            }
        }
    }

    fn intern_block(&self, stmts: Vec<ExprId>) -> ExprId {
        stmts.into_single_item().unwrap_or_else(|stmts| self.intern_expr(Expr::Block(Block { stmts })))
    }
}

impl<T: Intern + ?Sized> InternExt for T {}
