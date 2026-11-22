//! Port of `kodkod.engine.fol2sat.{LeafInterpreter, FOL2BoolTranslator, FOL2BoolCache}`.

use crate::annotate::{cache_records, Annotated, CacheRecords};
use crate::ast::*;
use crate::bool::*;
use crate::instance::{Bounds, TupleSet};
use std::collections::{BTreeMap, HashMap};

/// `LeafInterpreter`: relation bounds -> matrices of constants and primary variables.
pub struct Leaf {
    pub n: u32,
    pub lowers: HashMap<N, TupleSet>,
    pub uppers: HashMap<N, TupleSet>,
    /// relation -> (first variable, number of variables), in allocation order
    pub vars: Vec<(N, i32, i32)>,
    var_of: HashMap<N, i32>,
    pub ints: BTreeMap<i32, TupleSet>,
}

impl Leaf {
    /// `LeafInterpreter.exact(bounds, options, false)` (returns the interpreter and the number of primary variables)
    pub fn exact(b: &Bounds) -> Result<(Leaf, i32), String> {
        let mut vars = Vec::new();
        let mut var_of = HashMap::new();
        let mut max_lit = 1i32;
        for r in b.relations() {
            let (lo, hi) = match (b.lower.get(&r), b.upper.get(&r)) {
                (Some(l), Some(h)) => (l, h),
                _ => return Err("unresolved symbolic bound at translation".into()),
            };
            let n = hi.len() as i32 - lo.len() as i32;
            if n > 0 {
                vars.push((r, max_lit, n));
                var_of.insert(r, max_lit);
                max_lit += n;
            }
        }
        let leaf = Leaf {
            n: b.universe_size(),
            lowers: b.lower.clone(),
            uppers: b.upper.clone(),
            vars,
            var_of,
            ints: b.ints.clone(),
        };
        Ok((leaf, max_lit - 1))
    }

    /// `LeafInterpreter.overapproximating(bounds)` / `exact(instance)`: lowers = uppers = the given sets
    pub fn constant(n: u32, rels: HashMap<N, TupleSet>, ints: BTreeMap<i32, TupleSet>) -> Leaf {
        Leaf { n, lowers: rels.clone(), uppers: rels, vars: Vec::new(), var_of: HashMap::new(), ints }
    }

    pub fn first_var(&self, r: N) -> Option<i32> {
        self.var_of.get(&r).copied()
    }

    /// `interpret(Relation)`
    pub fn interpret_rel(&self, r: N, arity: u32) -> Result<Matrix, String> {
        let lo = self.lowers.get(&r).ok_or("Unbound relation")?;
        let hi = self.uppers.get(&r).ok_or("Unbound relation")?;
        let mut m = Matrix::empty(Dims::square(self.n, arity)?);
        for &i in &lo.idx {
            m.cells.insert(i, TRUE);
        }
        if hi.len() > lo.len() {
            let mut v = self.var_of[&r];
            for &i in &hi.idx {
                if !lo.contains(i) {
                    m.cells.insert(i, v);
                    v += 1;
                }
            }
        }
        Ok(m)
    }

    /// `interpret(ConstantExpression)`
    pub fn interpret_const(&self, c: ConstE) -> Result<Matrix, String> {
        let n = self.n;
        Ok(match c {
            ConstE::Univ => {
                let mut m = Matrix::empty(Dims::square(n, 1)?);
                for i in 0..n {
                    m.cells.insert(i, TRUE);
                }
                m
            }
            ConstE::Iden => {
                let mut m = Matrix::empty(Dims::square(n, 2)?);
                for i in 0..n {
                    m.cells.insert(i * n + i, TRUE);
                }
                m
            }
            ConstE::None => Matrix::empty(Dims::square(n, 1)?),
            ConstE::Ints => {
                let mut m = Matrix::empty(Dims::square(n, 1)?);
                for i in self.ints.keys() {
                    m.cells.insert(self.interpret_int(*i), TRUE);
                }
                m
            }
        })
    }

    pub fn interpret_int(&self, i: i32) -> u32 {
        self.ints[&i].idx[0]
    }
}

#[derive(Clone, Debug)]
pub enum Val {
    M(Matrix),
    B(BV),
    I(Int),
    L(Vec<Matrix>),
}

impl Val {
    fn m(self) -> Matrix {
        match self {
            Val::M(m) => m,
            _ => panic!("expected a matrix"),
        }
    }
    fn b(self) -> BV {
        match self {
            Val::B(b) => b,
            _ => panic!("expected a boolean"),
        }
    }
    fn i(self) -> Int {
        match self {
            Val::I(i) => i,
            _ => panic!("expected an int"),
        }
    }
}

struct Record {
    vars: Vec<N>,
    tuples: Vec<u32>,
    translation: Option<Val>,
}

/// `FOL2BoolTranslator` (+ `approximate` overrides when `approx` is set).
pub struct Fol2Bool<'a> {
    ast: &'a Ast,
    pub f: &'a mut Factory,
    leaf: &'a Leaf,
    env: Vec<(N, Matrix)>,
    records: HashMap<N, Record>,
    leaf_cache: HashMap<N, Matrix>,
    const_cache: [Option<Matrix>; 4],
    approx: bool,
}

impl<'a> Fol2Bool<'a> {
    pub fn new(ast: &'a Ast, ann: &Annotated, leaf: &'a Leaf, f: &'a mut Factory, approx: bool) -> Fol2Bool<'a> {
        let recs: CacheRecords = cache_records(ast, ann);
        let records = recs
            .into_iter()
            .map(|(n, vars)| {
                let k = vars.len();
                (n, Record { vars, tuples: vec![0; k], translation: None })
            })
            .collect();
        Fol2Bool { ast, f, leaf, env: Vec::new(), records, leaf_cache: HashMap::new(), const_cache: [None, None, None, None], approx }
    }

    /// Evaluation under an initial environment (Skolemizer `upperBound`).
    pub fn with_env(mut self, env: Vec<(N, Matrix)>) -> Self {
        self.env = env;
        self
    }

    fn env_lookup(&self, v: N) -> Option<&Matrix> {
        self.env.iter().rev().find(|(x, _)| *x == v).map(|(_, m)| m)
    }

    fn lookup(&self, n: N) -> Option<Val> {
        let r = self.records.get(&n)?;
        let t = r.translation.as_ref()?;
        for (i, v) in r.vars.iter().enumerate() {
            let m = self.env_lookup(*v)?;
            if m.get(r.tuples[i]) != TRUE {
                return None;
            }
        }
        Some(t.clone())
    }

    fn cache(&mut self, n: N, val: Val) -> Val {
        if self.records.contains_key(&n) {
            let mut tuples = Vec::new();
            let vars = self.records[&n].vars.clone();
            for v in &vars {
                let m = self.env_lookup(*v).expect("unbound cached variable");
                tuples.push(*m.cells.keys().next().unwrap_or(&0));
            }
            let r = self.records.get_mut(&n).unwrap();
            r.tuples = tuples;
            r.translation = Some(val.clone());
        }
        val
    }

    pub fn translate(&mut self, n: N) -> Result<Val, String> {
        self.visit(n)
    }

    fn mx(&mut self, n: N) -> Result<Matrix, String> {
        Ok(self.visit(n)?.m())
    }
    fn bx(&mut self, n: N) -> Result<BV, String> {
        Ok(self.visit(n)?.b())
    }
    fn ix(&mut self, n: N) -> Result<Int, String> {
        Ok(self.visit(n)?.i())
    }

    fn visit_decl(&mut self, d: N) -> Result<Matrix, String> {
        if let Some(v) = self.lookup(d) {
            return Ok(v.m());
        }
        let (m, e) = match self.ast.get(d) {
            Node::Decl(_, m, e) => (*m, *e),
            _ => unreachable!(),
        };
        if m != Mult::One {
            return Err("Analysis cannot be performed since it requires higher-order quantification that could not be skolemized.".into());
        }
        let r = self.mx(e)?;
        Ok(self.cache(d, Val::M(r)).m())
    }

    fn decl_parts(&self, d: N) -> (N, N) {
        match self.ast.get(d) {
            Node::Decl(v, _, e) => (*v, *e),
            _ => unreachable!(),
        }
    }

    fn visit(&mut self, n: N) -> Result<Val, String> {
        let node = self.ast.get(n).clone();
        Ok(match node {
            Node::Var { .. } => {
                let m = self.env_lookup(n).ok_or("Unbound variable")?;
                Val::M(m.clone())
            }
            Node::Rel(ref ri) => {
                if let Some(m) = self.leaf_cache.get(&n) {
                    return Ok(Val::M(m.clone()));
                }
                let m = self.leaf.interpret_rel(n, ri.arity)?;
                self.leaf_cache.insert(n, m.clone());
                Val::M(m)
            }
            Node::ConstE(c) => Val::M(self.constant(c)?),
            Node::BinE(op, l, r) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                if self.approx && op == EOp::Difference {
                    let x = self.visit(l)?;
                    return Ok(self.cache(n, x));
                }
                let a = self.mx(l)?;
                if self.approx && op == EOp::Override {
                    let b = self.mx(r)?;
                    let o = self.f.m_or(&a, &b);
                    return Ok(self.cache(n, Val::M(o)));
                }
                let b = self.mx(r)?;
                let ret = match op {
                    EOp::Union => self.f.m_or(&a, &b),
                    EOp::Intersection => self.f.m_and(&a, &b),
                    EOp::Difference => self.f.m_difference(&a, &b),
                    EOp::Override => self.f.m_override(&a, &b),
                    EOp::Join => self.f.m_dot(&a, &b)?,
                    EOp::Product => self.f.m_cross(&a, &b)?,
                    _ => return Err(format!("Unknown operator: {op:?}")),
                };
                self.cache(n, Val::M(ret))
            }
            Node::NaryE(op, cs) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                let first = self.mx(cs[0])?;
                let mut rest = Vec::with_capacity(cs.len() - 1);
                for &c in &cs[1..] {
                    rest.push(self.mx(c)?);
                }
                let rr: Vec<&Matrix> = rest.iter().collect();
                let ret = match op {
                    EOp::Union => self.f.m_or_n(&first, &rr),
                    EOp::Intersection => self.f.m_and_n(&first, &rr),
                    EOp::Override => self.f.m_override_n(&first, &rr),
                    EOp::Product => self.f.m_cross_n(&first, &rr)?,
                    _ => return Err(format!("Unknown associative operator: {op:?}")),
                };
                self.cache(n, Val::M(ret))
            }
            Node::UnE(op, e) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                let child = self.mx(e)?;
                let ret = match op {
                    EOp::Transpose => self.f.m_transpose(&child),
                    EOp::Closure => self.f.m_closure(&child)?,
                    EOp::ReflexiveClosure => {
                        let c = self.f.m_closure(&child)?;
                        let i = self.constant(ConstE::Iden)?;
                        self.f.m_or(&c, &i)
                    }
                    _ => return Err(format!("Unknown operator: {op:?}")),
                };
                self.cache(n, Val::M(ret))
            }
            Node::Compr(d, fm) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                if self.approx {
                    // approximate: TRUE.comprehension(decls)
                    let decls = self.ast.decls_list(d);
                    let mut ret = Matrix::empty(Dims::square(self.leaf.n, decls.len() as u32)?);
                    self.comprehension(&decls, None, 0, TRUE, 0, &mut ret)?;
                    return Ok(self.cache(n, Val::M(ret)));
                }
                let decls = self.ast.decls_list(d);
                let mut ret = Matrix::empty(Dims::square(self.leaf.n, decls.len() as u32)?);
                self.comprehension(&decls, Some(fm), 0, TRUE, 0, &mut ret)?;
                self.cache(n, Val::M(ret))
            }
            Node::IfE(c, t, e) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                if self.approx {
                    let a = self.mx(t)?;
                    let b = self.mx(e)?;
                    let o = self.f.m_or(&a, &b);
                    return Ok(self.cache(n, Val::M(o)));
                }
                let cond = self.bx(c)?;
                let a = self.mx(t)?;
                let b = self.mx(e)?;
                let r = self.f.m_choice(&a, cond, &b);
                self.cache(n, Val::M(r))
            }
            Node::Proj(..) => return Err("ProjectExpression is not supported by the exact pipeline".into()),
            Node::ConstF(b) => self.cache(n, Val::B(if b { TRUE } else { FALSE })),
            Node::Quant(q, d, body) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                let decls = self.ast.decls_list(d);
                let ret = match q {
                    Quant::All => {
                        let mut acc = Acc::new(Op::And);
                        self.all(&decls, body, 0, FALSE, &mut acc)?;
                        self.f.accumulate(&acc)
                    }
                    Quant::Some => {
                        let mut acc = Acc::new(Op::Or);
                        self.some(&decls, body, 0, TRUE, &mut acc)?;
                        self.f.accumulate(&acc)
                    }
                };
                self.cache(n, Val::B(ret))
            }
            Node::NaryF(op, cs) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                let bop = if op == FOp::And { Op::And } else { Op::Or };
                let sc = short_circuit(bop);
                let mut acc = Acc::new(bop);
                for c in cs {
                    let v = self.bx(c)?;
                    if acc.add(v) == sc {
                        break;
                    }
                }
                let r = self.f.accumulate(&acc);
                self.cache(n, Val::B(r))
            }
            Node::BinF(op, l, r) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                let a = self.bx(l)?;
                let b = self.bx(r)?;
                let ret = match op {
                    FOp::And => self.f.and(a, b),
                    FOp::Or => self.f.or(a, b),
                    FOp::Implies => self.f.implies(a, b),
                    FOp::Iff => self.f.iff(a, b),
                };
                self.cache(n, Val::B(ret))
            }
            Node::Not(x) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                let v = self.bx(x)?;
                self.cache(n, Val::B(-v))
            }
            Node::Cmp(op, l, r) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                let a = self.mx(l)?;
                let b = self.mx(r)?;
                let ret = match op {
                    CmpOp::Subset => self.f.m_subset(&a, &b),
                    CmpOp::Equals => self.f.m_eq(&a, &b),
                };
                self.cache(n, Val::B(ret))
            }
            Node::Mult(m, e) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                let child = self.mx(e)?;
                let ret = match m {
                    Mult::No => self.f.m_none(&child),
                    Mult::Some => self.f.m_some(&child),
                    Mult::One => self.f.m_one(&child),
                    Mult::Lone => self.f.m_lone(&child),
                    Mult::Set => return Err("Unknown multiplicity: set".into()),
                };
                self.cache(n, Val::B(ret))
            }
            Node::PAcyclic(..) | Node::PFunction(..) | Node::PTotal(..) => {
                return Err("relation predicates must be inlined before translation".into())
            }
            Node::I2E(op, ie) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                if self.approx {
                    match op {
                        CastOp::IntCast => {
                            let x = self.constant(ConstE::Ints)?;
                            return Ok(self.cache(n, Val::M(x)));
                        }
                        _ => {
                            let mut ret = Matrix::empty(Dims::square(self.leaf.n, 1)?);
                            let msb = self.f.bitwidth - 1;
                            for i in 0..msb {
                                let p = 1i32 << i;
                                if self.leaf.ints.contains_key(&p) {
                                    ret.set(self.leaf.interpret_int(p), TRUE);
                                }
                            }
                            let m = -1i32 << msb;
                            if self.leaf.ints.contains_key(&m) {
                                ret.set(self.leaf.interpret_int(m), TRUE);
                            }
                            return Ok(self.cache(n, Val::M(ret)));
                        }
                    }
                }
                let child = self.ix(ie)?;
                let mut ret = Matrix::empty(Dims::square(self.leaf.n, 1)?);
                match op {
                    CastOp::IntCast => {
                        let ints: Vec<i32> = self.leaf.ints.keys().copied().collect();
                        for i in ints {
                            let atom = self.leaf.interpret_int(i);
                            let cur = ret.get(atom);
                            let k = self.f.integer(i);
                            let e = self.f.int_eq(&child, &k);
                            let v = self.f.or(cur, e);
                            ret.set(atom, v);
                        }
                        ret.of = child.of;
                        ret.acc_of = child.acc_of;
                    }
                    CastOp::BitsetCast => {
                        let bits = child.twos_complement_bits(self.f.bitwidth);
                        let msb = bits.len() as i32 - 1;
                        for i in 0..msb {
                            let p = 1i32 << i;
                            if self.leaf.ints.contains_key(&p) {
                                ret.set(self.leaf.interpret_int(p), bits[i as usize]);
                            }
                        }
                        let m = -1i32 << msb;
                        if self.leaf.ints.contains_key(&m) {
                            ret.set(self.leaf.interpret_int(m), bits[msb as usize]);
                        }
                    }
                    _ => return Err(format!("Unknown cast operator: {op:?}")),
                }
                self.cache(n, Val::M(ret))
            }
            Node::IConst(v) => Val::I(self.f.integer(v)),
            Node::IfI(c, t, e) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                let cond = self.bx(c)?;
                let a = self.ix(t)?;
                let b = self.ix(e)?;
                let r = self.f.int_choice(&a, cond, &b);
                self.cache(n, Val::I(r))
            }
            Node::E2I(op, e) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                let m = self.mx(e)?;
                let ret = match op {
                    CastOp::Cardinality => self.f.m_cardinality(&m),
                    CastOp::Sum => {
                        let ints: Vec<i32> = self.leaf.ints.keys().copied().collect();
                        let mut it = ints.iter().copied();
                        self.sum_ints(&m, &mut it, 0, ints.len() as i32 - 1)
                    }
                    _ => return Err(format!("unknown operator: {op:?}")),
                };
                self.cache(n, Val::I(ret))
            }
            Node::BinI(op, l, r) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                let a = self.ix(l)?;
                let b = self.ix(r)?;
                let ret = match op {
                    IOp::Plus => self.f.int_plus(&a, &b),
                    IOp::Minus => self.f.int_minus(&a, &b),
                    IOp::Multiply => self.f.int_multiply(&a, &b),
                    IOp::Divide => self.f.int_divide(&a, &b),
                    IOp::Modulo => self.f.int_modulo(&a, &b),
                    IOp::And => self.f.int_and(&a, &b),
                    IOp::Or => self.f.int_or(&a, &b),
                    IOp::Xor => self.f.int_xor(&a, &b),
                    IOp::Shl => self.f.int_shl(&a, &b),
                    IOp::Shr => self.f.int_shr(&a, &b),
                    IOp::Sha => self.f.int_sha(&a, &b),
                    _ => return Err(format!("Unknown operator: {op:?}")),
                };
                self.cache(n, Val::I(ret))
            }
            Node::NaryI(op, cs) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                let first = self.ix(cs[0])?;
                let mut rest = Vec::new();
                for &c in &cs[1..] {
                    rest.push(self.ix(c)?);
                }
                let ret = match op {
                    IOp::Plus => self.f.int_apply_nary(true, &first, &rest),
                    IOp::Multiply => self.f.int_apply_nary(false, &first, &rest),
                    IOp::And => self.f.int_apply_bitwise(Op::And, &first, &rest),
                    IOp::Or => self.f.int_apply_bitwise(Op::Or, &first, &rest),
                    _ => return Err(format!("Unknown nary operator: {op:?}")),
                };
                self.cache(n, Val::I(ret))
            }
            Node::UnI(op, e) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                let child = self.ix(e)?;
                let ret = match op {
                    IOp::Neg => self.f.int_negate(&child),
                    IOp::Not => self.f.int_not(&child),
                    IOp::Abs => self.f.int_abs(&child),
                    IOp::Sgn => self.f.int_sgn(&child),
                    _ => return Err(format!("Unknown operator: {op:?}")),
                };
                self.cache(n, Val::I(ret))
            }
            Node::Sum(d, ie) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                let decls = self.ast.decls_list(d);
                let mut values: Vec<Int> = Vec::new();
                self.sum_decls(&decls, ie, 0, TRUE, &mut values)?;
                let mut sums = values.len();
                while sums > 1 {
                    let max = sums - 1;
                    let mut i = 0;
                    while i < max {
                        let s = self.f.int_plus(&values[i], &values[i + 1]);
                        values[i / 2] = s;
                        i += 2;
                    }
                    if max % 2 == 0 {
                        values[max / 2] = values[max].clone();
                    }
                    sums -= sums / 2;
                }
                let r = if values.is_empty() { self.f.integer(0) } else { values.swap_remove(0) };
                self.cache(n, Val::I(r))
            }
            Node::ICmp(op, l, r) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                let a = self.ix(l)?;
                let b = self.ix(r)?;
                let ret = match op {
                    ICmpOp::Eq => self.f.int_eq(&a, &b),
                    ICmpOp::Neq => self.f.int_neq(&a, &b),
                    ICmpOp::Lt => self.f.int_lt(&a, &b),
                    ICmpOp::Lte => self.f.int_lte(&a, &b),
                    ICmpOp::Gt => self.f.int_gt(&a, &b),
                    ICmpOp::Gte => self.f.int_gte(&a, &b),
                };
                self.cache(n, Val::B(ret))
            }
            Node::Decl(..) => Val::M(self.visit_decl(n)?),
            Node::Decls(ds) => {
                if let Some(v) = self.lookup(n) {
                    return Ok(v);
                }
                let mut ms = Vec::new();
                for d in ds {
                    ms.push(self.visit_decl(d)?);
                }
                self.cache(n, Val::L(ms))
            }
            Node::UTempF(..) | Node::BTempF(..) | Node::TempE(..) => {
                return Err("temporal formula reached the static translation".into())
            }
        })
    }

    /// `visit(ConstantExpression)` with the leaf cache (the constants are singletons in Java)
    fn constant(&mut self, c: ConstE) -> Result<Matrix, String> {
        let k = c as usize;
        if let Some(m) = &self.const_cache[k] {
            return Ok(m.clone());
        }
        let m = self.leaf.interpret_const(c)?;
        self.const_cache[k] = Some(m.clone());
        Ok(m)
    }

    fn sum_ints(&mut self, m: &Matrix, it: &mut dyn Iterator<Item = i32>, low: i32, high: i32) -> Int {
        if low > high {
            self.f.integer(0)
        } else if low == high {
            let i = it.next().unwrap();
            let v = m.get(self.leaf.interpret_int(i));
            self.f.integer_bit(i, v)
        } else {
            let mid = (low + high) / 2;
            let l = self.sum_ints(m, it, low, mid);
            let h = self.sum_ints(m, it, mid + 1, high);
            self.f.int_plus(&l, &h)
        }
    }

    fn comprehension(&mut self, decls: &[N], formula: Option<N>, cur: usize, dc: BV, partial: u32, out: &mut Matrix) -> Result<(), String> {
        if cur == decls.len() {
            let fv = match formula {
                Some(f) => self.bx(f)?,
                None => TRUE,
            };
            let v = self.f.and(dc, fv);
            out.set(partial, v);
            return Ok(());
        }
        let decl = decls[cur];
        let dt = self.visit_decl(decl)?;
        let position = (self.leaf.n as f64).powi((decls.len() - cur - 1) as i32) as u32;
        let (var, _) = self.decl_parts(decl);
        self.env.push((var, Matrix::empty(dt.dims)));
        for (&idx, &val) in &dt.cells {
            self.env.last_mut().unwrap().1.set(idx, TRUE);
            let ndc = self.f.and(val, dc);
            self.comprehension(decls, formula, cur + 1, ndc, partial + idx * position, out)?;
            self.env.last_mut().unwrap().1.set(idx, FALSE);
        }
        self.env.pop();
        Ok(())
    }

    fn all(&mut self, decls: &[N], formula: N, cur: usize, dc: BV, acc: &mut Acc) -> Result<(), String> {
        if acc.is_short_circuited() {
            return Ok(());
        }
        if decls.len() == cur {
            let fc = self.bx(formula)?;
            let v = self.f.or(dc, fc);
            acc.add(v);
            return Ok(());
        }
        let decl = decls[cur];
        let dt = self.visit_decl(decl)?;
        let (var, _) = self.decl_parts(decl);
        self.env.push((var, Matrix::empty(dt.dims)));
        for (&idx, &val) in &dt.cells {
            self.env.last_mut().unwrap().1.set(idx, TRUE);
            let ndc = self.f.or(-val, dc);
            self.all(decls, formula, cur + 1, ndc, acc)?;
            self.env.last_mut().unwrap().1.set(idx, FALSE);
        }
        self.env.pop();
        Ok(())
    }

    fn some(&mut self, decls: &[N], formula: N, cur: usize, dc: BV, acc: &mut Acc) -> Result<(), String> {
        if acc.is_short_circuited() {
            return Ok(());
        }
        if decls.len() == cur {
            let fc = self.bx(formula)?;
            let v = self.f.and(dc, fc);
            acc.add(v);
            return Ok(());
        }
        let decl = decls[cur];
        let dt = self.visit_decl(decl)?;
        let (var, _) = self.decl_parts(decl);
        self.env.push((var, Matrix::empty(dt.dims)));
        for (&idx, &val) in &dt.cells {
            self.env.last_mut().unwrap().1.set(idx, TRUE);
            let ndc = self.f.and(val, dc);
            self.some(decls, formula, cur + 1, ndc, acc)?;
            self.env.last_mut().unwrap().1.set(idx, FALSE);
        }
        self.env.pop();
        Ok(())
    }

    fn sum_decls(&mut self, decls: &[N], ie: N, cur: usize, dc: BV, values: &mut Vec<Int>) -> Result<(), String> {
        if decls.len() == cur {
            let v = self.ix(ie)?;
            let zero = self.f.integer(0);
            let c = self.f.int_choice(&v, dc, &zero);
            values.push(c);
            return Ok(());
        }
        let decl = decls[cur];
        let dt = self.visit_decl(decl)?;
        let (var, _) = self.decl_parts(decl);
        self.env.push((var, Matrix::empty(dt.dims)));
        for (&idx, &val) in &dt.cells {
            self.env.last_mut().unwrap().1.set(idx, TRUE);
            let ndc = self.f.and(val, dc);
            self.sum_decls(decls, ie, cur + 1, ndc, values)?;
            self.env.last_mut().unwrap().1.set(idx, FALSE);
        }
        self.env.pop();
        Ok(())
    }
}
