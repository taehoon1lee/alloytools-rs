//! Port of `kodkod.ast`: an arena of nodes; `N` (node id) is Java object identity (sharing matters to the
//! translation caches), so nodes are never deduplicated structurally.

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct N(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ConstE {
    Univ,
    Iden,
    None,
    Ints,
}

/// `ExprOperator`
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum EOp {
    Union,
    Intersection,
    Override,
    Product,
    Difference,
    Join,
    Transpose,
    Closure,
    ReflexiveClosure,
}

/// `IntOperator`
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IOp {
    Plus,
    Minus,
    Multiply,
    Divide,
    Modulo,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    Sha,
    Neg,
    Not,
    Abs,
    Sgn,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ICmpOp {
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CmpOp {
    Subset,
    Equals,
}

/// `Multiplicity`
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mult {
    No,
    Lone,
    One,
    Some,
    Set,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Quant {
    All,
    Some,
}

/// `FormulaOperator`
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FOp {
    And,
    Or,
    Iff,
    Implies,
}

/// `IntCastOperator` (IntToExprCast) / `ExprCastOperator` (ExprToIntCast)
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CastOp {
    IntCast,
    BitsetCast,
    Cardinality,
    Sum,
}

/// `TemporalOperator`
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TOp {
    Always,
    Eventually,
    After,
    Historically,
    Once,
    Before,
    Until,
    Releases,
    Since,
    Triggered,
    Prime,
}

#[derive(Clone, Debug)]
pub struct RelInfo {
    pub name: String,
    pub arity: u32,
    pub var: bool,
    pub atom: bool,
    pub skolem: bool,
}

#[derive(Clone, Debug)]
pub enum Node {
    Rel(RelInfo),
    Var { name: String, arity: u32 },
    ConstE(ConstE),
    ConstF(bool),
    BinE(EOp, N, N),
    UnE(EOp, N),
    NaryE(EOp, Vec<N>),
    Compr(N, N),
    IfE(N, N, N),
    Proj(N, Vec<N>),
    I2E(CastOp, N),
    E2I(CastOp, N),
    IConst(i32),
    BinI(IOp, N, N),
    NaryI(IOp, Vec<N>),
    UnI(IOp, N),
    Sum(N, N),
    IfI(N, N, N),
    ICmp(ICmpOp, N, N),
    Cmp(CmpOp, N, N),
    Mult(Mult, N),
    Quant(Quant, N, N),
    BinF(FOp, N, N),
    NaryF(FOp, Vec<N>),
    Not(N),
    PAcyclic(N),
    PFunction(N, N, Mult, N),
    PTotal(N, N, N, N),
    Decl(N, Mult, N),
    Decls(Vec<N>),
    UTempF(TOp, N),
    BTempF(TOp, N, N),
    TempE(TOp, N),
}

#[derive(Default, Clone)]
pub struct Ast {
    pub nodes: Vec<Node>,
    univ: Option<N>,
    iden: Option<N>,
    none: Option<N>,
    ints: Option<N>,
    tru: Option<N>,
    fls: Option<N>,
}

impl Ast {
    pub fn new() -> Ast {
        Ast::default()
    }
    pub fn add(&mut self, n: Node) -> N {
        let id = N(self.nodes.len() as u32);
        match &n {
            Node::ConstE(ConstE::Univ) if self.univ.is_none() => self.univ = Some(id),
            Node::ConstE(ConstE::Iden) if self.iden.is_none() => self.iden = Some(id),
            Node::ConstE(ConstE::None) if self.none.is_none() => self.none = Some(id),
            Node::ConstE(ConstE::Ints) if self.ints.is_none() => self.ints = Some(id),
            Node::ConstF(true) if self.tru.is_none() => self.tru = Some(id),
            Node::ConstF(false) if self.fls.is_none() => self.fls = Some(id),
            _ => {}
        }
        self.nodes.push(n);
        id
    }
    #[inline]
    pub fn get(&self, n: N) -> &Node {
        &self.nodes[n.0 as usize]
    }

    // ---- singletons (Expression.UNIV etc. are unique objects in Java)
    pub fn univ(&mut self) -> N {
        match self.univ {
            Some(n) => n,
            None => self.add(Node::ConstE(ConstE::Univ)),
        }
    }
    pub fn iden(&mut self) -> N {
        match self.iden {
            Some(n) => n,
            None => self.add(Node::ConstE(ConstE::Iden)),
        }
    }
    pub fn none(&mut self) -> N {
        match self.none {
            Some(n) => n,
            None => self.add(Node::ConstE(ConstE::None)),
        }
    }
    pub fn ints(&mut self) -> N {
        match self.ints {
            Some(n) => n,
            None => self.add(Node::ConstE(ConstE::Ints)),
        }
    }
    pub fn tru(&mut self) -> N {
        match self.tru {
            Some(n) => n,
            None => self.add(Node::ConstF(true)),
        }
    }
    pub fn fls(&mut self) -> N {
        match self.fls {
            Some(n) => n,
            None => self.add(Node::ConstF(false)),
        }
    }

    // ---- factories (Formula / Expression / Decl methods)
    pub fn binf(&mut self, l: N, op: FOp, r: N) -> N {
        self.add(Node::BinF(op, l, r))
    }
    /// `Formula.compose(op, Collection)`
    pub fn compose_f(&mut self, op: FOp, fs: &[N]) -> N {
        match fs.len() {
            0 => match op {
                FOp::And => self.tru(),
                _ => self.fls(),
            },
            1 => fs[0],
            2 => self.binf(fs[0], op, fs[1]),
            _ => self.add(Node::NaryF(op, fs.to_vec())),
        }
    }
    pub fn and_all(&mut self, fs: &[N]) -> N {
        self.compose_f(FOp::And, fs)
    }
    pub fn not(&mut self, f: N) -> N {
        self.add(Node::Not(f))
    }
    pub fn join(&mut self, a: N, b: N) -> N {
        self.add(Node::BinE(EOp::Join, a, b))
    }
    pub fn product(&mut self, a: N, b: N) -> N {
        self.add(Node::BinE(EOp::Product, a, b))
    }
    pub fn union(&mut self, a: N, b: N) -> N {
        self.add(Node::BinE(EOp::Union, a, b))
    }
    pub fn intersection(&mut self, a: N, b: N) -> N {
        self.add(Node::BinE(EOp::Intersection, a, b))
    }
    pub fn difference(&mut self, a: N, b: N) -> N {
        self.add(Node::BinE(EOp::Difference, a, b))
    }
    pub fn transpose(&mut self, a: N) -> N {
        self.add(Node::UnE(EOp::Transpose, a))
    }
    pub fn closure(&mut self, a: N) -> N {
        self.add(Node::UnE(EOp::Closure, a))
    }
    pub fn in_(&mut self, a: N, b: N) -> N {
        self.add(Node::Cmp(CmpOp::Subset, a, b))
    }
    pub fn eq(&mut self, a: N, b: N) -> N {
        self.add(Node::Cmp(CmpOp::Equals, a, b))
    }
    pub fn mult(&mut self, m: Mult, e: N) -> N {
        self.add(Node::Mult(m, e))
    }
    pub fn quantify(&mut self, q: Quant, decls: N, f: N) -> N {
        self.add(Node::Quant(q, decls, f))
    }
    pub fn comprehension(&mut self, decls: N, f: N) -> N {
        self.add(Node::Compr(decls, f))
    }
    pub fn declare(&mut self, var: N, m: Mult, e: N) -> N {
        self.add(Node::Decl(var, m, e))
    }
    pub fn one_of(&mut self, var: N, e: N) -> N {
        self.declare(var, Mult::One, e)
    }
    /// `Decls.and(decls)`: a flat Decls of both
    pub fn decls_and(&mut self, a: N, b: N) -> N {
        let mut v = self.decls_list(a);
        v.extend(self.decls_list(b));
        self.add(Node::Decls(v))
    }
    pub fn var(&mut self, name: &str, arity: u32) -> N {
        self.add(Node::Var { name: name.to_string(), arity })
    }
    pub fn rel(&mut self, name: &str, arity: u32) -> N {
        self.add(Node::Rel(RelInfo { name: name.to_string(), arity, var: false, atom: false, skolem: false }))
    }

    /// The decls of a Decls node (a Decl is a Decls of size one).
    pub fn decls_list(&self, d: N) -> Vec<N> {
        match self.get(d) {
            Node::Decls(v) => v.clone(),
            Node::Decl(..) => vec![d],
            other => panic!("not a decls node: {other:?}"),
        }
    }

    pub fn rel_info(&self, r: N) -> &RelInfo {
        match self.get(r) {
            Node::Rel(i) => i,
            other => panic!("not a relation: {other:?}"),
        }
    }

    /// `Expression.arity()`
    pub fn arity(&self, e: N) -> u32 {
        match self.get(e) {
            Node::Rel(i) => i.arity,
            Node::Var { arity, .. } => *arity,
            Node::ConstE(ConstE::Iden) => 2,
            Node::ConstE(_) => 1,
            Node::BinE(EOp::Product, a, b) => self.arity(*a) + self.arity(*b),
            Node::BinE(EOp::Join, a, b) => self.arity(*a) + self.arity(*b) - 2,
            Node::BinE(_, a, _) => self.arity(*a),
            Node::UnE(_, a) => self.arity(*a),
            Node::NaryE(EOp::Product, cs) => cs.iter().map(|c| self.arity(*c)).sum(),
            Node::NaryE(_, cs) => self.arity(cs[0]),
            Node::Compr(d, _) => self
                .decls_list(*d)
                .iter()
                .map(|x| match self.get(*x) {
                    Node::Decl(v, _, _) => self.arity(*v),
                    _ => 1,
                })
                .sum(),
            Node::IfE(_, t, _) => self.arity(*t),
            Node::Proj(_, cols) => cols.len() as u32,
            Node::I2E(..) => 1,
            Node::TempE(_, a) => self.arity(*a),
            other => panic!("arity of a non-expression: {other:?}"),
        }
    }
}
