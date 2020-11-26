use crate::ast::*;
use crate::frontend::{ArithmeticKind, ComparisonKind};
use crate::lower::LowerExt;
use crate::Lower;
use itertools::{Itertools, Position};
use std::fmt;

pub trait PrettyExt {
    fn pretty_print_expr(&self, function_name: IdentId, expr: ExprId) -> PrettyPrintExpr<'_, Self> {
        PrettyPrintExpr {
            db: self,
            function_name,
            indent: Indent { count: 0 },
            expr,
        }
    }

    fn pretty_print_function<'a>(&'a self, name: IdentId, function: &'a Function) -> PrettyPrintFunction<'a, Self> {
        PrettyPrintFunction { db: self, name, function }
    }

    fn pretty_print_type(&self, ty: TypeId) -> PrettyPrintType<'_, Self> {
        PrettyPrintType { db: self, ty }
    }
}

impl<T: ?Sized> PrettyExt for T {}

#[derive(Clone, Copy)]
struct Indent {
    count: u32,
}

impl<'a> fmt::Display for Indent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for _ in 0..self.count {
            f.write_str("    ")?;
        }

        Ok(())
    }
}

pub struct PrettyPrintExpr<'a, DB: ?Sized> {
    db: &'a DB,
    function_name: IdentId,
    indent: Indent,
    expr: ExprId,
}

impl<'a, DB: ?Sized> PrettyPrintExpr<'a, DB> {
    fn with_expr(&self, expr: ExprId) -> Self {
        Self { expr, ..*self }
    }

    fn enter(&self) -> Self {
        Self {
            indent: Indent { count: self.indent.count + 1 },
            ..*self
        }
    }
}

impl<'a, DB: Lower + ?Sized> fmt::Display for PrettyPrintExpr<'a, DB> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrintExprVisitor { p: self, f }.visit_expr(self.expr)
    }
}

struct PrettyPrintExprVisitor<'a, 'b, DB: ?Sized> {
    p: &'a PrettyPrintExpr<'a, DB>,
    f: &'a mut fmt::Formatter<'b>,
}

impl<'a, 'b, DB: Lower + ?Sized> ExprVisitor for PrettyPrintExprVisitor<'a, 'b, DB> {
    type Error = fmt::Error;

    fn lookup_expr(&self, expr: ExprId) -> Expr {
        self.p.db.lookup_intern_expr(expr)
    }

    fn visit_arithmetic(&mut self, _expr_id: ExprId, expr: Arithmetic) -> fmt::Result {
        let Arithmetic { lhs, op, rhs } = expr;

        let op = match op {
            ArithmeticKind::Add => "+",
            ArithmeticKind::Sub => "-",
            ArithmeticKind::Mul => "*",
            ArithmeticKind::Div => "/",
        };

        write!(self.f, "{} {} {}", self.p.with_expr(lhs), op, self.p.with_expr(rhs))
    }

    fn visit_assign(&mut self, _expr_id: ExprId, expr: Assign) -> fmt::Result {
        let Assign { lvalue, expr } = expr;
        write!(self.f, "{} = {}", self.p.with_expr(lvalue), self.p.with_expr(expr))
    }

    fn visit_block(&mut self, _expr_id: ExprId, expr: Block) -> fmt::Result {
        let Block { stmts } = expr;
        for expr in stmts.into_iter().with_position() {
            let (write_indent, write_nl) = match expr {
                Position::First(_) => (false, true),
                Position::Middle(_) => (true, true),
                Position::Last(_) => (true, false),
                Position::Only(_) => (false, false),
            };

            if write_indent {
                write!(self.f, "{}", self.p.indent)?;
            }

            write!(self.f, "{}", self.p.with_expr(expr.into_inner()))?;

            if write_nl {
                writeln!(self.f)?;
            }
        }

        Ok(())
    }

    fn visit_call(&mut self, _expr_id: ExprId, expr: Call) -> fmt::Result {
        let Call { env, name, args } = expr;
        let decl_env = self.p.db.binding_decl_env(self.p.function_name, env.unwrap(), name).unwrap();
        write!(
            self.f,
            "{}@{}({})",
            self.p.db.lookup_intern_ident(name),
            decl_env,
            args.iter().map(|&expr| self.p.with_expr(expr)).join(", ")
        )
    }

    fn visit_comparison(&mut self, _expr_id: ExprId, expr: Comparison) -> fmt::Result {
        let Comparison { lhs, op, rhs } = expr;

        let op = match op {
            ComparisonKind::Eq => "==",
            ComparisonKind::Ne => "!=",
            ComparisonKind::Lt => "<",
            ComparisonKind::Le => "<=",
            ComparisonKind::Gt => ">",
            ComparisonKind::Ge => ">=",
        };

        write!(self.f, "{} {} {}", self.p.with_expr(lhs), op, self.p.with_expr(rhs))
    }

    fn visit_deref(&mut self, _expr_id: ExprId, expr: Deref) -> fmt::Result {
        let Deref { expr } = expr;
        write!(self.f, "*{}", self.p.with_expr(expr))
    }

    fn visit_dot(&mut self, _expr_id: ExprId, expr: Dot) -> fmt::Result {
        let Dot { expr, field_name: name } = expr;
        write!(self.f, "{}.{}", self.p.with_expr(expr), self.p.db.lookup_intern_ident(name))
    }

    fn visit_global_data_addr(&mut self, _expr_id: ExprId, expr: GlobalDataAddr) -> fmt::Result {
        let GlobalDataAddr { name } = expr;
        write!(self.f, "&{}", self.p.db.lookup_intern_ident(name))
    }

    fn visit_identifier(&mut self, _expr_id: ExprId, expr: Identifier) -> fmt::Result {
        let Identifier { env, name } = expr;
        write!(self.f, "{}@", self.p.db.lookup_intern_ident(name))?;
        if let Some(env) = env {
            if let Ok(decl_env) = self.p.db.binding_decl_env(self.p.function_name, env, name) {
                write!(self.f, "{}", decl_env)
            } else {
                write!(self.f, "???")
            }
        } else {
            write!(self.f, "???")
        }
    }

    fn visit_if_else(&mut self, _expr_id: ExprId, expr: IfElse) -> fmt::Result {
        let IfElse { condition, then_body, else_body } = expr;
        let p = self.p.enter();
        writeln!(self.f, "if {} {{", self.p.with_expr(condition))?;
        writeln!(self.f, "{}{}", p.indent, p.with_expr(then_body))?;
        writeln!(self.f, "{}else {{", self.p.indent)?;
        writeln!(self.f, "{}{}", p.indent, p.with_expr(else_body))?;
        write!(self.f, "{}}}", self.p.indent)
    }

    fn visit_index(&mut self, _expr_id: ExprId, expr: Index) -> fmt::Result {
        let Index { base, offset } = expr;
        write!(self.f, "{}[{}]", self.p.with_expr(base), self.p.with_expr(offset))
    }

    fn visit_literal(&mut self, _expr_id: ExprId, expr: Literal) -> fmt::Result {
        let Literal { value } = expr;
        write!(self.f, "{}", value)
    }

    fn visit_scope(&mut self, _expr_id: ExprId, expr: Scope) -> fmt::Result {
        let Scope {
            scope_env: decl_env,
            decl_name,
            decl_expr,
            body,
        } = expr;
        let p = self.p.enter();
        writeln!(self.f, "{{")?;
        writeln!(
            self.f,
            "{}/* let */ {}@{} = {}",
            p.indent,
            self.p.db.lookup_intern_ident(decl_name),
            decl_env,
            p.with_expr(decl_expr)
        )?;
        writeln!(self.f, "{}{}", p.indent, p.with_expr(body))?;
        write!(self.f, "{}}}", self.p.indent)
    }

    fn visit_struct_init(&mut self, _expr_id: ExprId, expr: StructInit) -> fmt::Result {
        let StructInit { name, fields } = expr;
        let p = self.p.enter();
        writeln!(self.f, "{} {{", self.p.db.lookup_intern_ident(name))?;

        let mut fields = fields.into_iter().map(|(name, expr)| (self.p.db.lookup_intern_ident(name), expr)).collect::<Vec<_>>();
        fields.sort_by_key(|(name, _)| name.clone());

        for (name, expr) in fields {
            writeln!(self.f, "{}{}: {}", p.indent, name, p.with_expr(expr))?;
        }

        write!(self.f, "{}}}", self.p.indent)
    }

    fn visit_while_loop(&mut self, _expr_id: ExprId, expr: WhileLoop) -> fmt::Result {
        let WhileLoop { condition, body } = expr;
        let p = self.p.enter();
        writeln!(self.f, "while {} {{", self.p.with_expr(condition))?;
        writeln!(self.f, "{}{}", p.indent, p.with_expr(body))?;
        write!(self.f, "{}}}", self.p.indent)
    }
}

pub struct PrettyPrintFunction<'a, DB: ?Sized> {
    db: &'a DB,
    name: IdentId,
    function: &'a Function,
}

impl<'a, DB: Lower + ?Sized> fmt::Display for PrettyPrintFunction<'a, DB> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let &Function {
            ref signature,
            ref param_names,
            body,
        } = self.function;

        let &Signature { ref param_tys, return_ty } = signature;
        let name = self.db.lookup_intern_ident(self.name);

        let params = param_names.iter().zip(param_tys.iter()).format_with(", ", |(&name, &ty), f| {
            let name = self.db.lookup_intern_ident(name);
            let ty = self.db.pretty_print_type(ty);
            f(&format_args!("{}: {}", name, ty))
        });

        let ty = self.db.pretty_print_type(return_ty);
        writeln!(f, "fn {}({}) -> {} {{", name, params, ty)?;

        let indent = Indent { count: 1 };

        {
            let expr = PrettyPrintExpr {
                db: self.db,
                function_name: self.name,
                indent,
                expr: body,
            };
            writeln!(f, "{}{}", indent, expr)?;
        }

        writeln!(f, "}}")?;
        Ok(())
    }
}

pub struct PrettyPrintType<'a, DB: ?Sized> {
    db: &'a DB,
    ty: TypeId,
}

impl<'a, DB: ?Sized> PrettyPrintType<'a, DB> {
    fn with_type(&self, ty: TypeId) -> Self {
        Self { ty, ..*self }
    }
}

impl<'a, DB: Lower + ?Sized> fmt::Display for PrettyPrintType<'a, DB> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.db.lookup_intern_type(self.ty) {
            Type::Bool => f.write_str("bool"),
            Type::Integer(ty) => {
                let Integer { signed, bits } = ty;
                write!(f, "{}{}", if signed { "i" } else { "u" }, bits)
            }
            Type::Named(ty) => write!(f, "{}", self.db.lookup_intern_ident(ty)),
            Type::Number => f.write_str("<<number>>"),
            Type::Pointer(ty) => write!(f, "ptr<{}>", self.with_type(ty)),
            Type::Var(n) => write!(f, "'{}", char::from(b'a' + n as u8)),
            Type::Unit => f.write_str("()"),
        }
    }
}
