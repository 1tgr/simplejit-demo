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
    Dot(Box<Expr>, String),
    GlobalDataAddr(String),
    Identifier(String),
    IfElse(Box<Expr>, Vec<Expr>, Vec<Expr>),
    Index(Box<Expr>, Box<Expr>),
    Literal(i32),
    StructInit(String, Vec<(String, Box<Expr>)>),
    WhileLoop(Box<Expr>, Vec<Expr>),
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Type {
    I32,
    Named(String),
    Pointer(Box<Type>),
    U8,
    Unit,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Extern {
    pub params: Vec<(String, Type)>,
    pub return_ty: Type,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Function {
    pub params: Vec<(String, Type)>,
    pub return_ty: Type,
    pub stmts: Vec<Expr>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Struct {
    pub fields: Vec<(String, Type)>,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Item {
    Extern(Extern),
    Function(Function),
    Struct(Struct),
}

peg::parser!(pub grammar parser() for str {
    pub rule module() -> Vec<(String, Item)>
        = [' ' | '\t' | '\n']* items:((_ i:item() { i }) ** ([' ' | '\t' | '\n']*)) [' ' | '\t' | '\n']*  { items }

    rule item() -> (String, Item)
        = i:extern() { (i.0, Item::Extern(i.1)) }
        / i:function() { (i.0, Item::Function(i.1)) }
        / i:struct() { (i.0, Item::Struct(i.1)) }

    rule extern() -> (String, Extern)
        = "extern" _ "fn" _ name:identifier() _
        "(" params:((_ i:identifier() _ ":" _ t:ty() { (i, t) }) ** ",") ")" _
        "->" _
        return_ty:(_ t:ty() { t })
        { (name, Extern { params, return_ty }) }

    rule function() -> (String, Function)
        = "fn" _ name:identifier() _
        "(" params:((_ i:identifier() _ ":" _ t:ty() { (i, t) }) ** ",") ")" _
        "->" _
        return_ty:(_ t:ty() { t }) _
        "{" _ "\n"
        stmts:statements() _
        "}"
        { (name, Function { params, return_ty, stmts }) }

    rule struct() -> (String, Struct)
        = "struct" _ name:identifier() _ "{" _ "\n"
        fields:((_ i:identifier() _ ":" _ t:ty() _ "\n" { (i, t) })*)
        _ "}"
        { (name, Struct { fields }) }

    rule statements() -> Vec<Expr>
        = s:(statement()*) { s }

    rule statement() -> Expr
        = _ e:expression() _ "\n" { e }

    rule expression() -> Expr
        = if_else()
        / while_loop()
        / struct_init()
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
        a:@ _ "." _ b:identifier() { Expr::Dot(Box::new(a), b) }
        a:@ _ "[" _ b:expression() _ "]" { Expr::Index(Box::new(a), Box::new(b)) }
        i:identifier() _ "(" args:((_ e:expression() _ {e}) ** ",") ")" { Expr::Call(i, args) }
        i:identifier() { Expr::Identifier(i) }
        "*" _ a:@ { Expr::Deref(Box::new(a)) }
        l:literal() { l }
    }

    rule struct_init() -> Expr
        = i:identifier() _ "{" _ "\n"
        fields:((_ i:identifier() _ ":" _ e:expression() _ "\n" { (i, Box::new(e)) })*)
        _ "}"
        { Expr::StructInit(i, fields) }

    rule identifier() -> String
        = quiet!{ n:$(['a'..='z' | 'A'..='Z' | '_']['a'..='z' | 'A'..='Z' | '0'..='9' | '_' | ' ']*) { n.trim_end_matches(' ').to_owned() } }
        / expected!("identifier")

    rule ty() -> Type
        = "i32" { Type::I32 }
        / "u8" { Type::U8 }
        / "()" { Type::Unit }
        / "ptr" _ "<" _ t:ty() _ ">" { Type::Pointer(Box::new(t)) }
        / i:identifier() { Type::Named(i) }

    rule literal() -> Expr
        = n:$(['0'..='9']+) { Expr::Literal(n.parse().unwrap()) }
        / "&" i:identifier() { Expr::GlobalDataAddr(i) }

    rule _() =  quiet!{[' ' | '\t']*}
});
