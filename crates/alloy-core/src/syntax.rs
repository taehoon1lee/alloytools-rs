//! Port of the *surface* syntax built by the Java grammar actions in `parser/Alloy.cup` and
//! `CORE/parser/CompModule.java` (before name resolution). Nodes keep the source position of their
//! first token (1-based line/col like Java `Pos`). Semantic resolution (M3) builds a separate IR.
//!
//! Java counterparts: `Paragraph` ~ `CompModule.addSig/addFact/addFunc/addAssertion/addCommand/addOpen/addMacro`,
//! `Expr` ~ the `Expr*` builders reached from `Alloy.cup` productions (before `ExprList`/`ExprBinary` resolution).

/// 1-based source location of a node's first token.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Loc {
    pub line: i32,
    pub col: i32,
}

/// One `.als` file: optional `module` header followed by paragraphs in source order.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Module {
    /// `module a/b[X]` header, if present (name pieces joined by `/`).
    pub header: Option<ModuleHeader>,
    pub paragraphs: Vec<Paragraph>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ModuleHeader {
    pub loc: Loc,
    pub name: String,
    /// Formal parameters of a parametric module, e.g. `[exactly T]` -> `["T"]`.
    pub params: Vec<String>,
    /// Parameters declared `exactly` (their scope is forced to be exact).
    pub exact_params: Vec<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Paragraph {
    Open(Open),
    Sig(SigDecl),
    Enum(EnumDecl),
    Fact(Fact),
    Pred(Func),
    Fun(Func),
    Assert(Assert),
    Command(Command),
    /// Top-level `let name[params] = expr` (Java `ExprLet` macro, `CompModule.addMacro`).
    Macro(Macro),
}

/// `open util/ordering[S] as ord`.
#[derive(Debug, Clone, PartialEq)]
pub struct Open {
    pub loc: Loc,
    pub is_private: bool,
    /// Module path as written, e.g. `util/ordering`.
    pub name: String,
    /// Actual module arguments, each a name or expression.
    pub args: Vec<Expr>,
    pub alias: Option<String>,
}

/// Quantifier-like keywords that may prefix a signature.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct SigQuals {
    pub is_abstract: bool,
    pub lone: bool,
    pub one: bool,
    pub some: bool,
    pub is_private: bool,
    pub var: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SigExtends {
    /// `extends B`
    Extends(Expr),
    /// `in B + C` (subset signature)
    In(Vec<Expr>),
    /// `= B + C` (exact union signature; Java marker `"="`)
    Equal(Vec<Expr>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct SigDecl {
    pub loc: Loc,
    pub quals: SigQuals,
    /// `sig A, B` declares several sigs sharing one body.
    pub names: Vec<String>,
    pub extends: Option<SigExtends>,
    /// Field declarations inside `{ ... }`.
    pub fields: Vec<Decl>,
    /// Appended fact block `{ ... }` after the fields.
    pub appended_fact: Option<Vec<Expr>>,
}

/// `enum Color { Red, Green }`.
#[derive(Debug, Clone, PartialEq)]
pub struct EnumDecl {
    pub loc: Loc,
    pub is_private: bool,
    pub name: String,
    pub values: Vec<String>,
}

/// One declaration `[private] [disj] a, b: [var] [mult] expr`.
#[derive(Debug, Clone, PartialEq)]
pub struct Decl {
    pub loc: Loc,
    pub is_private: bool,
    pub disjoint: bool,
    pub var: bool,
    pub names: Vec<String>,
    /// The bounding expression, possibly a unary multiplicity (`lone A`, `set B`).
    pub expr: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Fact {
    pub loc: Loc,
    pub name: Option<String>,
    /// Conjuncts of the `{ ... }` block.
    pub body: Vec<Expr>,
}

/// `pred` or `fun`. For `pred`, `ret` is `None`; for `fun`, `body` is one expression.
#[derive(Debug, Clone, PartialEq)]
pub struct Func {
    pub loc: Loc,
    pub is_private: bool,
    /// Qualified name, e.g. `this/A.f` for sig-local functions (kept as written).
    pub name: String,
    pub params: Vec<Decl>,
    pub ret: Option<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Assert {
    pub loc: Loc,
    pub name: Option<String>,
    pub body: Vec<Expr>,
}

/// `let name[a, b] = e` or `let name[a, b] { conjuncts }` (Java `CompModule.addMacro`; params are plain names).
#[derive(Debug, Clone, PartialEq)]
pub struct Macro {
    pub loc: Loc,
    pub is_private: bool,
    pub name: String,
    pub params: Vec<String>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CommandTarget {
    /// `run name` / `check name` (a pred or assert name)
    Name(String),
    /// `run { ... }` anonymous block
    Block(Vec<Expr>),
}

/// `N [sig]`, `exactly N [sig]`, `N..M [sig]`, `N:I [sig]`, ... inside a `for` list (Java `CommandScope`).
/// `sig` is the user sig name, or `int` / `seq` / `steps` / `String` for the built-in scopes.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeScope {
    pub loc: Loc,
    pub sig: String,
    pub exactly: bool,
    pub start: i32,
    pub end: i32,
    pub increment: i32,
}

/// Everything after `for` / `but` / `expect` (surface form; defaults applied in M2).
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Scopes {
    /// Default scope from `for N`.
    pub overall: Option<i32>,
    /// `N int` / `N Int` bitwidth.
    pub bitwidth: Option<i32>,
    /// `N seq`.
    pub maxseq: Option<i32>,
    /// `N steps` (or `min..max steps`) for temporal models.
    pub steps: Option<Steps>,
    pub typescopes: Vec<TypeScope>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Steps {
    /// Lower trace length if written as `min..max steps`.
    pub min: Option<i32>,
    pub max: i32,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Command {
    pub loc: Loc,
    /// Label: `L: run ...` (the `ID : RUN` rewrite of `CompFilter`) or `run L foo` / `run L { }`.
    pub label: Option<String>,
    pub check: bool,
    pub target: CommandTarget,
    pub scopes: Scopes,
    /// `expect N`.
    pub expect: Option<i32>,
}

/// Quantifier keywords (`ExprQt.Op` in Java).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Quant {
    All,
    Some,
    No,
    Lone,
    One,
    Sum,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Const {
    Univ,
    Iden,
    None,
    /// The `Int` signature keyword.
    SigInt,
    /// The `String` signature keyword.
    SigString,
    /// The `this` keyword (`this/A` is a `Name`).
    This,
    /// `fun/min`, `fun/max`, `fun/next` (Java `ExprConstant.Op.MIN/MAX/NEXT`).
    IntMin,
    IntMax,
    IntNext,
}

/// Multiplicity written on one side of an arrow (`A one -> lone B`). `Set` is the default.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mult {
    Set,
    One,
    Lone,
    Some,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    /// `!` / `not`
    Not,
    No,
    Some,
    Lone,
    One,
    Set,
    Seq,
    Card,
    Transpose,
    Closure,
    ReflClosure,
    Neg,
    /// `sum e` / `int e` (Java `CAST2SIGINT(CAST2INT(e))`); also `int[e]`, `sum[e]`.
    IntCast,
    /// postfix `'`
    Prime,
    /// Java `EXACTLYOF`: the right side of a defined field `f = e`.
    ExactlyOf,
    Always,
    Eventually,
    Historically,
    Once,
    Before,
    After,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Or,
    Iff,
    Implies,
    And,
    Until,
    Releases,
    Since,
    Triggered,
    Equals,
    In,
    Lt,
    Le,
    Gt,
    Ge,
    Plus,
    Minus,
    Mul,
    Div,
    Rem,
    /// `fun/add`, `fun/sub`: integer addition/subtraction (Java `IPLUS`/`IMINUS`).
    IntPlus,
    IntMinus,
    Intersect,
    Override,
    /// `->` with the multiplicities written on the left and right side (`Set, Set` = plain `->`).
    Arrow(Mult, Mult),
    Join,
    DomainRestrict,
    RangeRestrict,
    Shl,
    Shr,
    Sha,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LetBind {
    pub loc: Loc,
    pub name: String,
    pub expr: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
    pub loc: Loc,
    pub kind: ExprKind,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    /// Identifier, possibly path-qualified (`util/ordering`, `this/A`); `@x` keeps the `@`.
    Name(String),
    Const(Const),
    Num(i32),
    /// String literal content without quote characters (lexer convention).
    Str(String),
    Unary(UnOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    /// `a[b, c]` box join (kept unresolved; M3 decides call vs join).
    BoxJoin(Box<Expr>, Vec<Expr>),
    /// `all x: A | body`, `sum x: A | expr`, ...; `body` is `Block` for `{ }` form.
    Quant(Quant, Vec<Decl>, Box<Expr>),
    /// `{ x: A | body }` set comprehension.
    Compr(Vec<Decl>, Box<Expr>),
    /// `let a = e1, b = e2 | body`.
    Let(Vec<LetBind>, Box<Expr>),
    /// `c => a else b`.
    IfElse(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `{ e1 e2 ... }` conjunction block.
    Block(Vec<Expr>),
    /// Parenthesised expression (kept so `(a) . b` stays grouped in the tree).
    Paren(Box<Expr>),
}

impl Expr {
    pub fn new(loc: Loc, kind: ExprKind) -> Self {
        Expr { loc, kind }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(s: &str) -> Expr {
        Expr::new(Loc { line: 1, col: 1 }, ExprKind::Name(s.to_string()))
    }

    #[test]
    fn builds_nested_surface_tree() {
        // `all x: A | x.f in B`  (shape only; parser comes in M1.3)
        let l = Loc { line: 2, col: 3 };
        let body = Expr::new(
            l,
            ExprKind::Binary(BinOp::In, Box::new(n("x")), Box::new(n("B"))),
        );
        let decl = Decl {
            loc: l,
            is_private: false,
            disjoint: false,
            var: false,
            names: vec!["x".into()],
            expr: n("A"),
        };
        let q = Expr::new(l, ExprKind::Quant(Quant::All, vec![decl], Box::new(body)));
        match &q.kind {
            ExprKind::Quant(Quant::All, decls, body) => {
                assert_eq!(decls[0].names, vec!["x".to_string()]);
                assert!(matches!(body.kind, ExprKind::Binary(BinOp::In, _, _)));
            }
            other => panic!("unexpected {other:?}"),
        }
    }

    #[test]
    fn module_default_is_empty() {
        let m = Module::default();
        assert!(m.header.is_none() && m.paragraphs.is_empty());
        assert_eq!(Scopes::default().overall, None);
    }
}
