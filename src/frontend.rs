#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum ArithmeticKind {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum ComparisonKind {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Expr {
    Arithmetic(Box<Expr>, ArithmeticKind, Box<Expr>),
    Assign(Box<Expr>, Box<Expr>),
    Call(String, Vec<Expr>),
    Comparison(Box<Expr>, ComparisonKind, Box<Expr>),
    Deref(Box<Expr>),
    GlobalDataAddr(String),
    Identifier(String),
    IfElse(Box<Expr>, Vec<Expr>, Vec<Expr>),
    Index(Box<Expr>, Box<Expr>),
    Literal(i32),
    WhileLoop(Box<Expr>, Vec<Expr>),
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Type {
    I32,
    Unit,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Function {
    pub params: Vec<(String, Type)>,
    pub return_ty: Type,
    pub stmts: Vec<Expr>,
}

peg::parser!(pub grammar parser() for str {
    pub rule module() -> Vec<(String, Function)>
        = [' ' | '\t' | '\n']* functions:((_ f:function() { f }) ** ([' ' | '\t' | '\n']*)) [' ' | '\t' | '\n']*  { functions }

    rule function() -> (String, Function)
        = "fn" _ name:identifier() _
        "(" params:((_ i:identifier() _ ":" _ t:ty() { (i, t) }) ** ",") ")" _
        "->" _
        return_ty:(_ t:ty() { t }) _
        "{" _ "\n"
        stmts:statements()
        _ "}"
        { (name, Function { params, return_ty, stmts }) }

    rule statements() -> Vec<Expr>
        = s:(statement()*) { s }

    rule statement() -> Expr
        = _ e:expression() _ "\n" { e }

    rule expression() -> Expr
        = if_else()
        / while_loop()
        / binary_op()

    rule if_else() -> Expr
        = "if" _ e:expression() _ "{" _ "\n"
        then_body:statements() _ "}" _ "else" _ "{" _ "\n"
        else_body:statements() _ "}"
        { Expr::IfElse(Box::new(e), then_body, else_body) }

    rule while_loop() -> Expr
        = "while" _ e:expression() _ "{" _ "\n"
        loop_body:statements() _ "}"
        { Expr::WhileLoop(Box::new(e), loop_body) }

    rule binary_op() -> Expr = precedence!{
        a:@ _ "=" _ b:expression() { Expr::Assign(Box::new(a), Box::new(b)) }
        --
        a:@ _ "==" _ b:(@) { Expr::Comparison(Box::new(a), ComparisonKind::Eq, Box::new(b)) }
        a:@ _ "!=" _ b:(@) { Expr::Comparison(Box::new(a), ComparisonKind::Ne, Box::new(b)) }
        a:@ _ "<"  _ b:(@) { Expr::Comparison(Box::new(a), ComparisonKind::Lt, Box::new(b)) }
        a:@ _ "<=" _ b:(@) { Expr::Comparison(Box::new(a), ComparisonKind::Le, Box::new(b)) }
        a:@ _ ">"  _ b:(@) { Expr::Comparison(Box::new(a), ComparisonKind::Gt, Box::new(b)) }
        a:@ _ ">=" _ b:(@) { Expr::Comparison(Box::new(a), ComparisonKind::Ge, Box::new(b)) }
        --
        a:@ _ "+" _ b:(@) { Expr::Arithmetic(Box::new(a), ArithmeticKind::Add, Box::new(b)) }
        a:@ _ "-" _ b:(@) { Expr::Arithmetic(Box::new(a), ArithmeticKind::Sub, Box::new(b)) }
        --
        a:@ _ "*" _ b:(@) { Expr::Arithmetic(Box::new(a), ArithmeticKind::Mul, Box::new(b)) }
        a:@ _ "/" _ b:(@) { Expr::Arithmetic(Box::new(a), ArithmeticKind::Div, Box::new(b)) }
        --
        a:@ _ "[" _ b:expression() _ "]" { Expr::Index(Box::new(a), Box::new(b)) }
        i:identifier() _ "(" args:((_ e:expression() _ {e}) ** ",") ")" { Expr::Call(i, args) }
        i:identifier() { Expr::Identifier(i) }
        "*" _ a:@ { Expr::Deref(Box::new(a)) }
        l:literal() { l }
    }

    rule identifier() -> String
        = quiet!{ n:$(['a'..='z' | 'A'..='Z' | '_']['a'..='z' | 'A'..='Z' | '0'..='9' | '_' | ' ']*) { n.trim_end_matches(' ').to_owned() } }
        / expected!("identifier")

    rule ty() -> Type
        = "i32" { Type::I32 }
        / "()" { Type::Unit }

    rule literal() -> Expr
        = n:$(['0'..='9']+) { Expr::Literal(n.parse().unwrap()) }
        / "&" i:identifier() { Expr::GlobalDataAddr(i) }

    rule _() =  quiet!{[' ' | '\t']*}
});
