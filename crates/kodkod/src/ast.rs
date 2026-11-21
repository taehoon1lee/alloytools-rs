//! Port of `kodkod/ast` (Expression, Formula, Variable, Relation, Decls) — the relational
//! logic that the Alloy translator produces. Trees are plain owned values (`Box`); the translator
//! builds each one once, so sharing is not needed at this stage.

pub type RelId = u32;
pub type VarId = u32;

/// Constant relations (Java `ConstantExpression`): `univ`, `iden`, `none`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Const {
    Univ,
    Iden,
    None,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// A relation declared in the bounds.
    Rel(RelId),
    /// A quantified or comprehension variable.
    Var(VarId),
    Const(Const),
    /// A literal set of tuples (Java `ConstantExpression` with a tuple set; used for `Int` atoms).
    Literal(crate::instance::TupleSet),
    Union(Box<Expr>, Box<Expr>),
    Intersection(Box<Expr>, Box<Expr>),
    Difference(Box<Expr>, Box<Expr>),
    /// `a ++ b` (override).
    Override(Box<Expr>, Box<Expr>),
    /// `a . b` (relational join).
    Join(Box<Expr>, Box<Expr>),
    Product(Box<Expr>, Box<Expr>),
    Transpose(Box<Expr>),
    /// `^a`.
    Closure(Box<Expr>),
    /// `*a` = `iden + ^a`.
    ReflexiveClosure(Box<Expr>),
    /// `f => a else b`.
    IfThenElse(Box<Formula>, Box<Expr>, Box<Expr>),
    /// `{ x: A, y: B | f }`.
    Comprehension(Vec<Decl>, Box<Formula>),
    /// The integer `i` as a set: the atom with value `i` if it is `i` (Kodkod `IntToExprCast`).
    IntToExpr(Box<IntExpr>),
}

/// Integer expressions over the bitwidth of the bounds (Kodkod `IntExpression`). Arithmetic wraps around.
#[derive(Debug, Clone, PartialEq)]
pub enum IntExpr {
    Const(i64),
    /// `#e`: number of tuples of `e`.
    Card(Box<Expr>),
    /// `int[e]`: sum of the values of the integer atoms in `e` (unary).
    Sum(Box<Expr>),
    Add(Box<IntExpr>, Box<IntExpr>),
    Sub(Box<IntExpr>, Box<IntExpr>),
    Mul(Box<IntExpr>, Box<IntExpr>),
    Neg(Box<IntExpr>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntCmp {
    Eq,
    Lt,
    Le,
}

/// One declaration `x: e` of a quantifier or comprehension (Java `Decl`).
#[derive(Debug, Clone, PartialEq)]
pub struct Decl {
    pub var: VarId,
    pub domain: Expr,
    /// Disjoint declarations (`disj x, y: e`) are handled by the translator's caller.
    pub disjoint: bool,
    /// `set` multiplicity: the variable ranges over the *subsets* of `domain` (Alloy `x: set e`).
    pub set: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Quantifier {
    All,
    Some,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Multiplicity {
    /// `some e`
    Some,
    /// `no e`
    No,
    /// `one e`
    One,
    /// `lone e`
    Lone,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Formula {
    True,
    False,
    /// `a in b`
    Subset(Expr, Expr),
    /// `a = b`
    Equal(Expr, Expr),
    Multiplicity(Multiplicity, Expr),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Iff(Box<Formula>, Box<Formula>),
    Quantified(Quantifier, Vec<Decl>, Box<Formula>),
    /// Comparison of two integer expressions.
    IntCompare(IntCmp, IntExpr, IntExpr),
}

impl Expr {
    pub fn union(a: Expr, b: Expr) -> Expr {
        Expr::Union(Box::new(a), Box::new(b))
    }
    pub fn join(a: Expr, b: Expr) -> Expr {
        Expr::Join(Box::new(a), Box::new(b))
    }
    pub fn product(a: Expr, b: Expr) -> Expr {
        Expr::Product(Box::new(a), Box::new(b))
    }
}
