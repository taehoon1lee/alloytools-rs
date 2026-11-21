//! Port of `kodkod/engine/fol2sat/FOL2BoolTranslator` + `LeafInterpreter` + `Solver`.
//!
//! A relation becomes a [`BoolMatrix`]: a sparse map from tuples to boolean values. Tuples in the
//! lower bound are TRUE, tuples outside the upper bound are absent (FALSE), and every other upper
//! bound tuple gets a fresh primary SAT variable (allocated in tuple order, as Kodkod's
//! `LeafInterpreter` does). Expressions are evaluated bottom-up with the relational operators;
//! quantifiers and comprehensions are unrolled over the tuples of their domains.

use std::collections::{BTreeMap, HashMap};

use satsolver::{BatSat, SatSolver};

use crate::ast::{Const, Decl, Expr, Formula, IntCmp, IntExpr, Multiplicity, Quantifier, VarId};
use crate::bool::{BoolFactory, BoolVal};
use crate::instance::{Bounds, Instance, TupleSet};

/// Sparse boolean relation: absent tuples are FALSE.
#[derive(Debug, Clone, PartialEq)]
pub struct BoolMatrix {
    pub arity: usize,
    pub entries: BTreeMap<Vec<u32>, BoolVal>,
}

impl BoolMatrix {
    pub fn empty(arity: usize) -> Self {
        BoolMatrix {
            arity,
            entries: BTreeMap::new(),
        }
    }

    fn singleton(t: Vec<u32>) -> Self {
        let mut m = BoolMatrix::empty(t.len());
        m.entries.insert(t, BoolVal::TRUE);
        m
    }

    fn get(&self, t: &[u32]) -> BoolVal {
        self.entries.get(t).copied().unwrap_or(BoolVal::FALSE)
    }
}

/// Translation state for one problem (bounds fixed, formula added via [`Translator::formula`]).
pub struct Translator<'a, S: SatSolver> {
    pub bounds: &'a Bounds,
    pub f: BoolFactory<S>,
    /// Matrix of every relation, indexed by relation id.
    rels: Vec<BoolMatrix>,
    env: Env,
    /// Memo of translated sub-expressions: (node address, binding ids of its free variables) -> matrix
    /// (Kodkod's `FOL2BoolCache`). Nodes are never freed while they are translated, so addresses are stable.
    expr_cache: HashMap<(usize, Vec<u64>), BoolMatrix>,
    fv_cache: HashMap<usize, std::rc::Rc<Vec<VarId>>>,
    /// > 0 while translating temporary expressions (no caching by address).
    no_cache: u32,
    /// SAT variables of skolem bits (branched on right after the primary variables).
    skolem_vars: Vec<u32>,
    /// Number of relation (primary) variables allocated at construction: SAT variables `1..=base_primary`.
    base_primary: u32,
    /// Number of primary variables (free upper-bound tuples).
    pub primary_vars: usize,
    /// Polarity of the formula being translated (true = positive).
    pol: bool,
    /// > 0 where a formula occurs in both polarities (no skolemization there).
    no_skolem: u32,
    /// Effectively universal quantifiers around the current formula (Kodkod's `skolemDepth = 0` stops there).
    univ_depth: u32,
}

impl<'a, S: SatSolver> Translator<'a, S> {
    pub fn new(bounds: &'a Bounds, sat: S) -> Self {
        let mut f = BoolFactory::new(sat);
        let mut rels = Vec::with_capacity(bounds.relations.len());
        let mut primary_vars = 0;
        for rb in &bounds.relations {
            let mut m = BoolMatrix::empty(rb.arity);
            for t in &rb.upper.tuples {
                let v = if rb.lower.contains(t) {
                    BoolVal::TRUE
                } else {
                    primary_vars += 1;
                    f.new_var()
                };
                m.entries.insert(t.clone(), v);
            }
            rels.push(m);
        }
        Translator {
            bounds,
            f,
            rels,
            env: Env::default(),
            expr_cache: HashMap::new(),
            fv_cache: HashMap::new(),
            no_cache: 0,
            skolem_vars: Vec::new(),
            base_primary: primary_vars as u32,
            primary_vars,
            pol: true,
            no_skolem: 0,
            univ_depth: 0,
        }
    }

    fn primary_vars_base(&self) -> u32 {
        self.base_primary
    }

    fn n(&self) -> u32 {
        self.bounds.universe.size() as u32
    }

    /// Evaluates a relational expression (memoized per free-variable binding).
    pub fn expr(&mut self, e: &Expr) -> Result<BoolMatrix, String> {
        if self.no_cache > 0 || matches!(e, Expr::Rel(_) | Expr::Var(_) | Expr::Const(_) | Expr::Literal(_)) {
            return self.expr_uncached(e);
        }
        let ptr = e as *const Expr as usize;
        let fvs = match self.fv_cache.get(&ptr) {
            Some(v) => v.clone(),
            None => {
                let mut out = std::collections::BTreeSet::new();
                fv_expr(e, &mut Vec::new(), &mut out);
                let v = std::rc::Rc::new(out.into_iter().collect::<Vec<VarId>>());
                self.fv_cache.insert(ptr, v.clone());
                v
            }
        };
        let key: Vec<u64> = fvs.iter().map(|v| self.env.id(*v)).collect();
        if let Some(m) = self.expr_cache.get(&(ptr, key.clone())) {
            return Ok(m.clone());
        }
        let m = self.expr_uncached(e)?;
        self.expr_cache.insert((ptr, key), m.clone());
        Ok(m)
    }

    fn expr_uncached(&mut self, e: &Expr) -> Result<BoolMatrix, String> {
        Ok(match e {
            Expr::Rel(r) => self
                .rels
                .get(*r as usize)
                .cloned()
                .ok_or_else(|| format!("unknown relation {r}"))?,
            Expr::Var(v) => self
                .env
                .get(v)
                .cloned()
                .ok_or_else(|| format!("unbound variable {v}"))?,
            Expr::Const(Const::Univ) => {
                let mut m = BoolMatrix::empty(1);
                for a in 0..self.n() {
                    m.entries.insert(vec![a], BoolVal::TRUE);
                }
                m
            }
            Expr::Const(Const::Iden) => {
                let mut m = BoolMatrix::empty(2);
                for a in 0..self.n() {
                    m.entries.insert(vec![a, a], BoolVal::TRUE);
                }
                m
            }
            Expr::Const(Const::None) => BoolMatrix::empty(1),
            Expr::Literal(ts) => {
                let mut m = BoolMatrix::empty(ts.arity);
                for t in &ts.tuples {
                    m.entries.insert(t.clone(), BoolVal::TRUE);
                }
                m
            }
            Expr::Union(a, b) => {
                let (a, b) = (self.expr(a)?, self.expr(b)?);
                same_arity(&a, &b, "union")?;
                let mut out = a.clone();
                for (t, v) in &b.entries {
                    let cur = out.get(t);
                    let nv = self.f.or2(cur, *v);
                    out.entries.insert(t.clone(), nv);
                }
                out
            }
            Expr::Intersection(a, b) => {
                let (a, b) = (self.expr(a)?, self.expr(b)?);
                same_arity(&a, &b, "intersection")?;
                let mut out = BoolMatrix::empty(a.arity);
                for (t, v) in &a.entries {
                    let w = b.get(t);
                    let nv = self.f.and2(*v, w);
                    out.entries.insert(t.clone(), nv);
                }
                out
            }
            Expr::Difference(a, b) => {
                let (a, b) = (self.expr(a)?, self.expr(b)?);
                same_arity(&a, &b, "difference")?;
                let mut out = BoolMatrix::empty(a.arity);
                for (t, v) in &a.entries {
                    let nb = self.f.not(b.get(t));
                    let nv = self.f.and2(*v, nb);
                    out.entries.insert(t.clone(), nv);
                }
                out
            }
            Expr::Override(a, b) => {
                // a ++ b = b + (a restricted to tuples whose key (all columns but the last) is not
                // the key of a tuple of b). Arity 1 is plain union.
                let (a, b) = (self.expr(a)?, self.expr(b)?);
                same_arity(&a, &b, "override")?;
                if a.arity == 1 {
                    return Ok(self.union_matrices(&a, &b));
                }
                let k = a.arity - 1;
                let mut keys: BTreeMap<Vec<u32>, Vec<BoolVal>> = BTreeMap::new();
                for (t, v) in &b.entries {
                    keys.entry(t[..k].to_vec()).or_default().push(*v);
                }
                let mut out = b.clone();
                for (t, v) in &a.entries {
                    let kept = match keys.get(&t[..k]).cloned() {
                        None => *v,
                        Some(vals) => {
                            let any = self.f.or(&vals);
                            let nany = self.f.not(any);
                            self.f.and2(*v, nany)
                        }
                    };
                    let cur = out.get(t);
                    let nv = self.f.or2(cur, kept);
                    out.entries.insert(t.clone(), nv);
                }
                out
            }
            Expr::Join(a, b) => {
                let (a, b) = (self.expr(a)?, self.expr(b)?);
                self.join_m(&a, &b)?
            }
            Expr::Product(a, b) => {
                let (a, b) = (self.expr(a)?, self.expr(b)?);
                let mut out = BoolMatrix::empty(a.arity + b.arity);
                for (ta, va) in &a.entries {
                    for (tb, vb) in &b.entries {
                        let mut key = ta.clone();
                        key.extend_from_slice(tb);
                        let v = self.f.and2(*va, *vb);
                        out.entries.insert(key, v);
                    }
                }
                out
            }
            Expr::Transpose(a) => {
                let a = self.expr(a)?;
                if a.arity != 2 {
                    return Err("transpose needs a binary relation".into());
                }
                let mut out = BoolMatrix::empty(2);
                for (t, v) in &a.entries {
                    out.entries.insert(vec![t[1], t[0]], *v);
                }
                out
            }
            Expr::Closure(a) => {
                let a = self.expr(a)?;
                self.closure(a)?
            }
            Expr::ReflexiveClosure(a) => {
                let a = self.expr(a)?;
                let c = self.closure(a)?;
                let iden = self.expr(&Expr::Const(Const::Iden))?;
                let mut out = c;
                for (t, v) in &iden.entries {
                    let cur = out.get(t);
                    let nv = self.f.or2(cur, *v);
                    out.entries.insert(t.clone(), nv);
                }
                out
            }
            Expr::IfThenElse(c, a, b) => {
                self.no_skolem += 1;
                let cond = self.formula(c);
                self.no_skolem -= 1;
                let cond = cond?;
                let (a, b) = (self.expr(a)?, self.expr(b)?);
                same_arity(&a, &b, "if-then-else")?;
                let mut keys: Vec<Vec<u32>> = a.entries.keys().cloned().collect();
                keys.extend(b.entries.keys().cloned());
                keys.sort();
                keys.dedup();
                let mut out = BoolMatrix::empty(a.arity);
                for t in keys {
                    let v = self.f.ite(cond, a.get(&t), b.get(&t));
                    out.entries.insert(t, v);
                }
                out
            }
            Expr::IntToExpr(ie) => {
                let bits = self.int_expr(ie)?;
                let w = bits.len();
                let mut out = BoolMatrix::empty(1);
                for k in 0..(1u64 << w) {
                    let value = self.bounds.int_min + k as i64;
                    let eqv = self.bits_eq_const(&bits, value);
                    if eqv != BoolVal::FALSE {
                        out.entries.insert(vec![self.bounds.int_start + k as u32], eqv);
                    }
                }
                out
            }
            Expr::Comprehension(decls, body) => {
                let body: &Formula = body;
                let mut key = Vec::new();
                let mut leaves = Vec::new();
                if decls.iter().any(|d| d.set) {
                    return Err("set declarations in comprehensions are not supported yet".into());
                }
                self.leaves(decls, 0, BoolVal::TRUE, &mut key, false, &mut leaves, &mut |t: &mut Self, g| {
                    t.no_skolem += 1;
                    let b = t.formula(&body);
                    t.no_skolem -= 1;
                    let b = b?;
                    Ok(t.f.and2(g, b))
                })?;
                let arity = self.comprehension_arity(decls)?;
                let mut out = BoolMatrix::empty(arity);
                for (k, v) in leaves {
                    let cur = out.get(&k);
                    let nv = self.f.or2(cur, v);
                    out.entries.insert(k, nv);
                }
                out
            }
        })
    }

    fn width(&self) -> Result<usize, String> {
        match self.bounds.bitwidth {
            0 => Err("integers are not part of this problem (bitwidth 0)".into()),
            w => Ok(w as usize),
        }
    }

    /// Two's-complement bits of `v` truncated to `w` bits (LSB first).
    fn const_bits(v: i64, w: usize) -> Vec<BoolVal> {
        (0..w).map(|i| BoolVal::Const((v >> i) & 1 == 1)).collect()
    }

    /// Evaluates an integer expression to `w` bits (wrap-around arithmetic, as Kodkod's default).
    fn int_expr(&mut self, e: &IntExpr) -> Result<Vec<BoolVal>, String> {
        let w = self.width()?;
        Ok(match e {
            IntExpr::Const(c) => Self::const_bits(*c, w),
            IntExpr::Card(x) => {
                let m = self.expr(x)?;
                let mut acc = Self::const_bits(0, w);
                for v in m.entries.values().copied().collect::<Vec<_>>() {
                    let mut one = vec![BoolVal::FALSE; w];
                    one[0] = v;
                    acc = self.add_bits(&acc, &one);
                }
                acc
            }
            IntExpr::Sum(x) => {
                let m = self.expr(x)?;
                let (start, min) = (self.bounds.int_start, self.bounds.int_min);
                let n = 1u64 << w;
                let mut acc = Self::const_bits(0, w);
                let entries: Vec<(Vec<u32>, BoolVal)> = m.entries.iter().map(|(t, v)| (t.clone(), *v)).collect();
                for (t, v) in entries {
                    let a = t[0] as u64;
                    if t[0] < start || a - start as u64 >= n {
                        continue;
                    }
                    let value = min + (a - start as u64) as i64;
                    let part: Vec<BoolVal> = Self::const_bits(value, w)
                        .into_iter()
                        .map(|b| self.f.and2(v, b))
                        .collect();
                    acc = self.add_bits(&acc, &part);
                }
                acc
            }
            IntExpr::Add(a, b) => {
                let (a, b) = (self.int_expr(a)?, self.int_expr(b)?);
                self.add_bits(&a, &b)
            }
            IntExpr::Sub(a, b) => {
                let (a, b) = (self.int_expr(a)?, self.int_expr(b)?);
                let nb = self.neg_bits(&b);
                self.add_bits(&a, &nb)
            }
            IntExpr::Mul(a, b) => {
                let (a, b) = (self.int_expr(a)?, self.int_expr(b)?);
                self.mul_bits(&a, &b)
            }
            IntExpr::Div(a, b) => {
                let (a, b) = (self.int_expr(a)?, self.int_expr(b)?);
                self.divrem_bits(&a, &b).0
            }
            IntExpr::Rem(a, b) => {
                let (a, b) = (self.int_expr(a)?, self.int_expr(b)?);
                self.divrem_bits(&a, &b).1
            }
            IntExpr::Neg(a) => {
                let a = self.int_expr(a)?;
                self.neg_bits(&a)
            }
            IntExpr::SumOver(decls, body) => {
                let w = self.bounds.bitwidth as usize;
                let mut key = Vec::new();
                let mut leaves: Vec<(Vec<u32>, BoolVal)> = Vec::new();
                let mut terms: Vec<Vec<BoolVal>> = Vec::new();
                let body: &IntExpr = body;
                self.leaves(decls, 0, BoolVal::TRUE, &mut key, false, &mut leaves, &mut |t: &mut Self, g| {
                    let v = t.int_expr(&body)?;
                    let masked: Vec<BoolVal> = v.iter().map(|b| t.f.and2(g, *b)).collect();
                    terms.push(masked);
                    Ok(BoolVal::TRUE)
                })?;
                let mut acc = vec![BoolVal::FALSE; w];
                for t in terms {
                    acc = self.add_bits(&acc, &t);
                }
                acc
            }
        })
    }

    /// Signed division (truncating toward zero) and remainder (sign of the dividend) by shift-and-subtract
    /// on absolute values.
    fn divrem_bits(&mut self, a: &[BoolVal], b: &[BoolVal]) -> (Vec<BoolVal>, Vec<BoolVal>) {
        let w = a.len();
        if w == 0 {
            return (Vec::new(), Vec::new());
        }
        let (sa, sb) = (a[w - 1], b[w - 1]);
        let na = self.neg_bits(a);
        let nb = self.neg_bits(b);
        let abs_a: Vec<BoolVal> = (0..w).map(|i| self.f.ite(sa, na[i], a[i])).collect();
        let abs_b: Vec<BoolVal> = (0..w).map(|i| self.f.ite(sb, nb[i], b[i])).collect();
        let mut bext = abs_b.clone();
        bext.push(BoolVal::FALSE);
        let mut rem: Vec<BoolVal> = vec![BoolVal::FALSE; w + 1];
        let mut q = vec![BoolVal::FALSE; w];
        for i in (0..w).rev() {
            rem.insert(0, abs_a[i]);
            rem.truncate(w + 1);
            // rem - b = rem + !b + 1; the final carry says rem >= b
            let mut carry = BoolVal::TRUE;
            let mut diff = Vec::with_capacity(w + 1);
            for k in 0..=w {
                let nbk = self.f.not(bext[k]);
                let x = self.f.ite(rem[k], self.f.not(nbk), nbk);
                let nc = self.f.not(carry);
                diff.push(self.f.ite(x, nc, carry));
                let ab = self.f.and2(rem[k], nbk);
                let aob = self.f.or2(rem[k], nbk);
                let cab = self.f.and2(carry, aob);
                carry = self.f.or2(ab, cab);
            }
            q[i] = carry;
            rem = (0..=w).map(|k| self.f.ite(carry, diff[k], rem[k])).collect();
        }
        rem.truncate(w);
        let nq = self.neg_bits(&q);
        let nr = self.neg_bits(&rem);
        let diff_sign = self.f.ite(sa, self.f.not(sb), sb);
        let quot = (0..w).map(|i| self.f.ite(diff_sign, nq[i], q[i])).collect();
        let remd = (0..w).map(|i| self.f.ite(sa, nr[i], rem[i])).collect();
        (quot, remd)
    }

    fn add_bits(&mut self, a: &[BoolVal], b: &[BoolVal]) -> Vec<BoolVal> {
        let mut carry = BoolVal::FALSE;
        let mut out = Vec::with_capacity(a.len());
        for i in 0..a.len() {
            let nb = self.f.not(b[i]);
            let x = self.f.ite(a[i], nb, b[i]); // a xor b
            let nc = self.f.not(carry);
            let sum = self.f.ite(x, nc, carry); // x xor carry
            let ab = self.f.and2(a[i], b[i]);
            let aob = self.f.or2(a[i], b[i]);
            let cab = self.f.and2(carry, aob);
            carry = self.f.or2(ab, cab);
            out.push(sum);
        }
        out
    }

    fn neg_bits(&mut self, a: &[BoolVal]) -> Vec<BoolVal> {
        let w = a.len();
        let inv: Vec<BoolVal> = a.iter().map(|x| self.f.not(*x)).collect();
        self.add_bits(&inv, &Self::const_bits(1, w))
    }

    fn mul_bits(&mut self, a: &[BoolVal], b: &[BoolVal]) -> Vec<BoolVal> {
        let w = a.len();
        let mut acc = Self::const_bits(0, w);
        for i in 0..w {
            let mut part = vec![BoolVal::FALSE; w];
            for j in i..w {
                part[j] = self.f.and2(b[i], a[j - i]);
            }
            acc = self.add_bits(&acc, &part);
        }
        acc
    }

    fn bits_eq(&mut self, a: &[BoolVal], b: &[BoolVal]) -> BoolVal {
        let parts: Vec<BoolVal> = a.iter().zip(b).map(|(x, y)| self.f.iff(*x, *y)).collect();
        self.f.and(&parts)
    }

    fn bits_eq_const(&mut self, a: &[BoolVal], v: i64) -> BoolVal {
        let c = Self::const_bits(v, a.len());
        self.bits_eq(a, &c)
    }

    /// Signed `a < b`: flip the sign bits, then compare as unsigned from the most significant bit.
    fn bits_lt(&mut self, a: &[BoolVal], b: &[BoolVal]) -> BoolVal {
        let w = a.len();
        let mut a = a.to_vec();
        let mut b = b.to_vec();
        a[w - 1] = self.f.not(a[w - 1]);
        b[w - 1] = self.f.not(b[w - 1]);
        let mut res = BoolVal::FALSE;
        for i in 0..w {
            let na = self.f.not(a[i]);
            let lt = self.f.and2(na, b[i]);
            let eq = self.f.iff(a[i], b[i]);
            let keep = self.f.and2(eq, res);
            res = self.f.or2(lt, keep);
        }
        res
    }

    /// Transitive closure by repeated squaring: `R := R ∪ R.R` for ceil(log2 n) rounds.
    fn closure(&mut self, a: BoolMatrix) -> Result<BoolMatrix, String> {
        if a.arity != 2 {
            return Err("closure needs a binary relation".into());
        }
        let mut r = a;
        let mut span = 1u64;
        while span < self.n() as u64 {
            let sq = self.join_m(&r, &r)?;
            r = self.union_matrices(&r, &sq);
            span *= 2;
        }
        Ok(r)
    }

    /// Relational join of two evaluated matrices: `a.b`.
    fn join_m(&mut self, a: &BoolMatrix, b: &BoolMatrix) -> Result<BoolMatrix, String> {
        if a.arity + b.arity < 3 {
            return Err(format!("join needs an expression of arity 2 or more (arities {} and {})", a.arity, b.arity));
        }
        let mut acc: BTreeMap<Vec<u32>, Vec<BoolVal>> = BTreeMap::new();
        for (ta, va) in &a.entries {
            let last = *ta.last().unwrap();
            for (tb, vb) in &b.entries {
                if tb[0] != last {
                    continue;
                }
                let mut key = ta[..ta.len() - 1].to_vec();
                key.extend_from_slice(&tb[1..]);
                let v = self.f.and2(*va, *vb);
                acc.entry(key).or_default().push(v);
            }
        }
        let mut out = BoolMatrix::empty(a.arity + b.arity - 2);
        for (k, vals) in acc {
            let v = self.f.or(&vals);
            out.entries.insert(k, v);
        }
        Ok(out)
    }

    /// Static arity of a comprehension: the sum of its declarations' domain arities.
    fn comprehension_arity(&self, decls: &[Decl]) -> Result<usize, String> {
        let mut vars = HashMap::new();
        let mut total = 0;
        for d in decls {
            let a = self.static_arity(&d.domain, &mut vars)?;
            vars.insert(d.var, a);
            total += a;
        }
        Ok(total)
    }

    /// Arity of an expression from the relation arities of the bounds (no evaluation).
    pub fn static_arity(&self, e: &Expr, vars: &mut HashMap<VarId, usize>) -> Result<usize, String> {
        Ok(match e {
            Expr::Rel(r) => self.bounds.rel(*r).arity,
            Expr::Var(v) => match vars.get(v) {
                Some(a) => *a,
                // variables of enclosing quantifiers are bound in the environment
                None => self.env.get(v).map(|m| m.arity).ok_or_else(|| format!("unbound variable {v}"))?,
            },
            Expr::Const(Const::Univ) | Expr::Const(Const::None) => 1,
            Expr::Const(Const::Iden) => 2,
            Expr::Literal(ts) => ts.arity,
            Expr::Union(a, _) | Expr::Intersection(a, _) | Expr::Difference(a, _) | Expr::Override(a, _) => {
                self.static_arity(a, vars)?
            }
            Expr::Join(a, b) => self.static_arity(a, vars)? + self.static_arity(b, vars)? - 2,
            Expr::Product(a, b) => self.static_arity(a, vars)? + self.static_arity(b, vars)?,
            Expr::Transpose(_) | Expr::Closure(_) | Expr::ReflexiveClosure(_) => 2,
            Expr::IntToExpr(_) => 1,
            Expr::IfThenElse(_, a, _) => self.static_arity(a, vars)?,
            Expr::Comprehension(decls, _) => {
                let mut total = 0;
                for d in decls {
                    let a = self.static_arity(&d.domain, vars)?;
                    vars.insert(d.var, a);
                    total += a;
                }
                total
            }
        })
    }

    fn union_matrices(&mut self, a: &BoolMatrix, b: &BoolMatrix) -> BoolMatrix {
        let mut out = a.clone();
        for (t, v) in &b.entries {
            let cur = out.get(t);
            let nv = self.f.or2(cur, *v);
            out.entries.insert(t.clone(), nv);
        }
        out
    }

    /// Evaluates a formula to a boolean value.
    pub fn formula(&mut self, f: &Formula) -> Result<BoolVal, String> {
        Ok(match f {
            Formula::True => BoolVal::TRUE,
            Formula::False => BoolVal::FALSE,
            Formula::Subset(a, b) => {
                let (a, b) = (self.expr(a)?, self.expr(b)?);
                same_arity(&a, &b, "in")?;
                self.subset(&a, &b)
            }
            Formula::Equal(a, b) => {
                let (a, b) = (self.expr(a)?, self.expr(b)?);
                same_arity(&a, &b, "=")?;
                // One IFF per tuple of the union of the bounds (Kodkod's equality of boolean matrices).
                let mut keys: Vec<Vec<u32>> = a.entries.keys().cloned().collect();
                keys.extend(b.entries.keys().cloned());
                keys.sort();
                keys.dedup();
                let mut vals = Vec::with_capacity(keys.len());
                for t in &keys {
                    vals.push(self.f.iff(a.get(t), b.get(t)));
                }
                self.f.and(&vals)
            }
            Formula::Multiplicity(m, e) => {
                let e = self.expr(e)?;
                let vals: Vec<BoolVal> = e.entries.values().copied().collect();
                match m {
                    Multiplicity::Some => self.f.or(&vals),
                    Multiplicity::No => {
                        let s = self.f.or(&vals);
                        self.f.not(s)
                    }
                    Multiplicity::Lone => self.at_most_one(&vals),
                    Multiplicity::One => {
                        let s = self.f.or(&vals);
                        let l = self.at_most_one(&vals);
                        self.f.and2(s, l)
                    }
                }
            }
            Formula::Not(a) => {
                self.pol = !self.pol;
                let a = self.formula(a);
                self.pol = !self.pol;
                let a = a?;
                self.f.not(a)
            }
            Formula::And(items) => {
                let vals = items.iter().map(|x| self.formula(x)).collect::<Result<Vec<_>, _>>()?;
                self.f.and(&vals)
            }
            Formula::Or(items) => {
                let vals = items.iter().map(|x| self.formula(x)).collect::<Result<Vec<_>, _>>()?;
                self.f.or(&vals)
            }
            Formula::Implies(a, b) => {
                self.pol = !self.pol;
                let a = self.formula(a);
                self.pol = !self.pol;
                let a = a?;
                let b = self.formula(b)?;
                self.f.implies(a, b)
            }
            Formula::Iff(a, b) => {
                self.no_skolem += 1;
                let r = (|| Ok::<_, String>((self.formula(a)?, self.formula(b)?)))();
                self.no_skolem -= 1;
                let (a, b) = r?;
                self.f.iff(a, b)
            }
            Formula::IntCompare(cmp, a, b) => {
                let (a, b) = (self.int_expr(a)?, self.int_expr(b)?);
                match cmp {
                    IntCmp::Eq => self.bits_eq(&a, &b),
                    IntCmp::Lt => self.bits_lt(&a, &b),
                    IntCmp::Le => {
                        let lt = self.bits_lt(&a, &b);
                        let eq = self.bits_eq(&a, &b);
                        self.f.or2(lt, eq)
                    }
                }
            }
            Formula::Quantified(q, decls, body)
                if self.no_skolem == 0 && self.univ_depth == 0 && ((*q == Quantifier::Some) == self.pol) =>
            {
                self.skolemize(*q, decls, body)?
            }
            Formula::Quantified(q, decls, body) => {
                // Duality for set declarations: all s ⊆ E. f  ==  not (some s ⊆ E. not f). The existential
                // side is solved with witness bits, so no subset enumeration is needed.
                if *q == Quantifier::All && decls.iter().any(|d| d.set) {
                    let dual = Formula::Quantified(
                        Quantifier::Some,
                        decls.clone(),
                        Box::new(Formula::Not(body.clone())),
                    );
                    // the temporary tree must not be cached by address
                    self.no_cache += 1;
                    let r = self.formula(&Formula::Not(Box::new(dual)));
                    self.no_cache -= 1;
                    return r;
                }
                let body: &Formula = body;
                let mut key = Vec::new();
                let mut leaves = Vec::new();
                let all = *q == Quantifier::All;
                let univ = (*q == Quantifier::All) == self.pol;
                self.leaves(decls, 0, BoolVal::TRUE, &mut key, all, &mut leaves, &mut |t: &mut Self, g| {
                    if univ {
                        t.univ_depth += 1;
                    }
                    let b = t.formula(&body);
                    if univ {
                        t.univ_depth -= 1;
                    }
                    let b = b?;
                    Ok(if all { t.f.implies(g, b) } else { t.f.and2(g, b) })
                })?;
                let vals: Vec<BoolVal> = leaves.into_iter().map(|(_, v)| v).collect();
                if all {
                    self.f.and(&vals)
                } else {
                    self.f.or(&vals)
                }
            }
        })
    }

    /// Skolemization (Kodkod `Skolemizer`, depth 0): an existential quantifier (`some` in positive position, `all`
    /// in negative position) not inside a universal one becomes fresh free bits per variable, each restricted
    /// to its domain (exactly one tuple unless it is a `set` declaration).
    fn skolemize(&mut self, q: Quantifier, decls: &[Decl], body: &Formula) -> Result<BoolVal, String> {
        let mut cons = Vec::new();
        let mut saved = Vec::new();
        for d in decls {
            let dom = self.expr(&d.domain)?;
            let mut m = BoolMatrix::empty(dom.arity);
            let mut bits = Vec::new();
            for (t, v) in &dom.entries {
                if *v == BoolVal::FALSE {
                    continue;
                }
                let bit = self.f.new_var();
                if let BoolVal::Lit(l) = bit {
                    self.skolem_vars.push(l.unsigned_abs());
                }
                self.primary_vars += 1;
                if *v != BoolVal::TRUE {
                    cons.push(self.f.implies(bit, *v));
                }
                m.entries.insert(t.clone(), bit);
                bits.push(bit);
            }
            if !d.set {
                cons.push(self.f.or(&bits));
                cons.push(self.at_most_one(&bits));
            }
            saved.push((d.var, self.env.insert(d.var, m)));
        }
        let b = self.formula(body);
        for (v, old) in saved.into_iter().rev() {
            match old {
                Some(m) => {
                    self.env.insert(v, m);
                }
                None => {
                    self.env.remove(&v);
                }
            }
        }
        let b = b?;
        Ok(if q == Quantifier::Some {
            cons.push(b);
            self.f.and(&cons)
        } else {
            let c = self.f.and(&cons);
            self.f.implies(c, b)
        })
    }

    /// `a ⊆ b` for matrices of the same arity.
    fn subset(&mut self, a: &BoolMatrix, b: &BoolMatrix) -> BoolVal {
        let mut vals = Vec::new();
        for (t, v) in &a.entries {
            let w = b.get(t);
            vals.push(self.f.implies(*v, w));
        }
        self.f.and(&vals)
    }

    /// At most one of the values is true (pairwise).
    fn at_most_one(&mut self, vals: &[BoolVal]) -> BoolVal {
        // Linear encoding: v_i -> no earlier value holds (a running OR), instead of all pairs.
        let mut parts = Vec::new();
        let mut earlier = BoolVal::FALSE;
        for &v in vals {
            let ne = self.f.not(earlier);
            parts.push(self.f.implies(v, ne));
            earlier = self.f.or2(earlier, v);
        }
        self.f.and(&parts)
    }

    /// Enumerates the bindings of `decls` (each domain evaluated under the bindings so far).
    /// At every leaf the callback gets the guard (all memberships hold) and returns the leaf value;
    /// `out` collects `(key, value)` where the key is the concatenated tuples of the bound variables.
    ///
    /// Set declarations (`x: set e`): an existential one becomes free witness bits restricted to `e`
    /// (the SAT solver chooses the witness, one set of bits per enclosing binding); a universal one
    /// enumerates the subsets of the possible tuples of `e` (limited to 12 possible tuples).
    fn leaves(
        &mut self,
        decls: &[Decl],
        i: usize,
        guard: BoolVal,
        key: &mut Vec<u32>,
        all: bool,
        out: &mut Vec<(Vec<u32>, BoolVal)>,
        f: &mut dyn FnMut(&mut Self, BoolVal) -> Result<BoolVal, String>,
    ) -> Result<(), String> {
        if i == decls.len() {
            let v = f(self, guard)?;
            out.push((key.clone(), v));
            return Ok(());
        }
        let d = &decls[i];
        let dom = self.expr(&d.domain)?;
        let saved = self.env.get(&d.var).cloned();
        if d.set {
            if all {
                let items: Vec<(Vec<u32>, BoolVal)> = dom
                    .entries
                    .iter()
                    .filter(|(_, v)| **v != BoolVal::FALSE)
                    .map(|(t, v)| (t.clone(), *v))
                    .collect();
                if items.len() > 12 {
                    return Err("universal quantification over a set of more than 12 possible tuples".into());
                }
                for mask in 0u32..(1u32 << items.len()) {
                    let mut g = guard;
                    let mut m = BoolMatrix::empty(dom.arity);
                    for (j, (t, v)) in items.iter().enumerate() {
                        if mask & (1 << j) != 0 {
                            g = self.f.and2(g, *v);
                            m.entries.insert(t.clone(), BoolVal::TRUE);
                        }
                    }
                    if g == BoolVal::FALSE {
                        continue;
                    }
                    self.env.insert(d.var, m);
                    self.leaves(decls, i + 1, g, key, all, out, f)?;
                }
            } else {
                let mut m = BoolMatrix::empty(dom.arity);
                for (t, v) in &dom.entries {
                    let bit = self.f.new_var();
                    let w = self.f.and2(bit, *v);
                    if w != BoolVal::FALSE {
                        m.entries.insert(t.clone(), w);
                    }
                }
                self.env.insert(d.var, m);
                self.leaves(decls, i + 1, guard, key, all, out, f)?;
            }
        } else {
            for (t, v) in &dom.entries {
                let g = self.f.and2(guard, *v);
                if g == BoolVal::FALSE {
                    continue;
                }
                self.env.insert(d.var, BoolMatrix::singleton(t.clone()));
                let mark = key.len();
                key.extend_from_slice(t);
                self.leaves(decls, i + 1, g, key, all, out, f)?;
                key.truncate(mark);
            }
        }
        match saved {
            Some(m) => self.env.insert(d.var, m),
            None => self.env.remove(&d.var),
        };
        Ok(())
    }
}

/// Variable environment with a unique id per binding (used as cache key).
#[derive(Default)]
struct Env {
    m: HashMap<VarId, (BoolMatrix, u64)>,
    next: u64,
}

impl Env {
    fn get(&self, v: &VarId) -> Option<&BoolMatrix> {
        self.m.get(v).map(|(m, _)| m)
    }
    fn id(&self, v: VarId) -> u64 {
        self.m.get(&v).map_or(0, |(_, i)| *i)
    }
    fn insert(&mut self, v: VarId, m: BoolMatrix) -> Option<BoolMatrix> {
        self.next += 1;
        self.m.insert(v, (m, self.next)).map(|(m, _)| m)
    }
    fn remove(&mut self, v: &VarId) -> Option<BoolMatrix> {
        self.m.remove(v).map(|(m, _)| m)
    }
}

fn fv_expr(e: &Expr, bound: &mut Vec<VarId>, out: &mut std::collections::BTreeSet<VarId>) {
    match e {
        Expr::Rel(_) | Expr::Const(_) | Expr::Literal(_) => {}
        Expr::Var(v) => {
            if !bound.contains(v) {
                out.insert(*v);
            }
        }
        Expr::Union(a, b)
        | Expr::Intersection(a, b)
        | Expr::Difference(a, b)
        | Expr::Override(a, b)
        | Expr::Join(a, b)
        | Expr::Product(a, b) => {
            fv_expr(a, bound, out);
            fv_expr(b, bound, out);
        }
        Expr::Transpose(a) | Expr::Closure(a) | Expr::ReflexiveClosure(a) => fv_expr(a, bound, out),
        Expr::IfThenElse(c, a, b) => {
            fv_formula(c, bound, out);
            fv_expr(a, bound, out);
            fv_expr(b, bound, out);
        }
        Expr::Comprehension(decls, body) => fv_decls(decls, body, bound, out),
        Expr::IntToExpr(i) => fv_int(i, bound, out),
    }
}

fn fv_decls(decls: &[Decl], body: &Formula, bound: &mut Vec<VarId>, out: &mut std::collections::BTreeSet<VarId>) {
    let mark = bound.len();
    for d in decls {
        fv_expr(&d.domain, bound, out);
        bound.push(d.var);
    }
    fv_formula(body, bound, out);
    bound.truncate(mark);
}

fn fv_int(i: &IntExpr, bound: &mut Vec<VarId>, out: &mut std::collections::BTreeSet<VarId>) {
    match i {
        IntExpr::Const(_) => {}
        IntExpr::Card(e) | IntExpr::Sum(e) => fv_expr(e, bound, out),
        IntExpr::Add(a, b) | IntExpr::Sub(a, b) | IntExpr::Mul(a, b) | IntExpr::Div(a, b) | IntExpr::Rem(a, b) => {
            fv_int(a, bound, out);
            fv_int(b, bound, out);
        }
        IntExpr::Neg(a) => fv_int(a, bound, out),
        IntExpr::SumOver(decls, body) => {
            let mark = bound.len();
            for d in decls {
                fv_expr(&d.domain, bound, out);
                bound.push(d.var);
            }
            fv_int(body, bound, out);
            bound.truncate(mark);
        }
    }
}

fn fv_formula(f: &Formula, bound: &mut Vec<VarId>, out: &mut std::collections::BTreeSet<VarId>) {
    match f {
        Formula::True | Formula::False => {}
        Formula::Subset(a, b) | Formula::Equal(a, b) => {
            fv_expr(a, bound, out);
            fv_expr(b, bound, out);
        }
        Formula::Multiplicity(_, e) => fv_expr(e, bound, out),
        Formula::Not(a) => fv_formula(a, bound, out),
        Formula::And(items) | Formula::Or(items) => {
            for x in items {
                fv_formula(x, bound, out);
            }
        }
        Formula::Implies(a, b) | Formula::Iff(a, b) => {
            fv_formula(a, bound, out);
            fv_formula(b, bound, out);
        }
        Formula::Quantified(_, decls, body) => fv_decls(decls, body, bound, out),
        Formula::IntCompare(_, a, b) => {
            fv_int(a, bound, out);
            fv_int(b, bound, out);
        }
    }
}

fn same_arity(a: &BoolMatrix, b: &BoolMatrix, op: &str) -> Result<(), String> {
    if a.arity == b.arity {
        Ok(())
    } else {
        Err(format!("{op} of expressions with different arities ({} and {})", a.arity, b.arity))
    }
}

/// Does swapping atoms `a` and `b` map every relation's lower and upper bound onto itself?
pub fn interchangeable(bounds: &Bounds, a: u32, b: u32) -> bool {
    let swap = |t: &Vec<u32>| -> Vec<u32> {
        t.iter().map(|&x| if x == a { b } else if x == b { a } else { x }).collect()
    };
    bounds.relations.iter().all(|rb| {
        let up: std::collections::BTreeSet<Vec<u32>> = rb.upper.tuples.iter().map(swap).collect();
        let lo: std::collections::BTreeSet<Vec<u32>> = rb.lower.tuples.iter().map(swap).collect();
        up == rb.upper.tuples && lo == rb.lower.tuples
    })
}

/// Symmetry classes: sets of mutually interchangeable atoms (Kodkod's `SymmetryDetector` partitions, found here
/// by testing transpositions). Atoms in `ordered_atoms` are excluded. Classes (and atoms in them) ascend.
pub fn symmetry_classes(bounds: &Bounds) -> Vec<Vec<u32>> {
    let n = bounds.universe.size() as u32;
    // signature: degree of each atom in every relation's bounds (a cheap class key; verified below)
    let mut key: Vec<Vec<usize>> = vec![Vec::new(); n as usize];
    for rb in &bounds.relations {
        let mut lo = vec![0usize; n as usize];
        let mut up = vec![0usize; n as usize];
        for t in &rb.lower.tuples {
            for &a in t {
                lo[a as usize] += 1;
            }
        }
        for t in &rb.upper.tuples {
            for &a in t {
                up[a as usize] += 1;
            }
        }
        for a in 0..n as usize {
            key[a].push(lo[a]);
            key[a].push(up[a]);
        }
    }
    let mut groups: std::collections::BTreeMap<Vec<usize>, Vec<u32>> = std::collections::BTreeMap::new();
    for a in 0..n {
        if bounds.ordered_atoms.contains(&a) {
            continue;
        }
        groups.entry(key[a as usize].clone()).or_default().push(a);
    }
    let mut classes: Vec<Vec<u32>> = Vec::new();
    for atoms in groups.values() {
        let mut local: Vec<Vec<u32>> = Vec::new();
        for &a in atoms {
            match local.iter_mut().find(|cl| interchangeable(bounds, cl[0], a)) {
                Some(cl) => cl.push(a),
                None => local.push(vec![a]),
            }
        }
        classes.extend(local.into_iter().filter(|cl| cl.len() > 1));
    }
    classes.sort();
    classes
}

/// Portfolio attempt without symmetry breaking.
const NO_SBP: u8 = 255;

/// Java `SymmetryBreaker.generateSBP` (symmetry = 20): for every adjacent pair `(prev, cur)` of a symmetry class,
/// the bits of the non-constant relations (sorted by arity, then name; whole relations are taken until 20 bit
/// pairs are collected) must be lexicographically at most their image under swapping `prev` and `cur`.
fn add_symmetry_breaking<S: SatSolver>(tr: &mut Translator<'_, S>, order: u8) {
    let pred_length: usize = 20;
    let bounds = tr.bounds;
    let classes = if order == NO_SBP { Vec::new() } else { symmetry_classes(bounds) };
    if classes.is_empty() {
        return;
    }
    let mut class_of: Vec<usize> = vec![usize::MAX; bounds.universe.size()];
    for (ci, cl) in classes.iter().enumerate() {
        for &a in cl {
            class_of[a as usize] = ci;
        }
    }
    // non-constant relations with the classes their upper bound ranges over
    let mut rels: Vec<(usize, usize, String, std::collections::BTreeSet<usize>)> = Vec::new();
    for (r, rb) in bounds.relations.iter().enumerate() {
        if rb.upper.tuples.len() == rb.lower.tuples.len() {
            continue;
        }
        let mut reps = std::collections::BTreeSet::new();
        for t in &rb.upper.tuples {
            for &a in t {
                let ci = class_of[a as usize];
                if ci != usize::MAX {
                    reps.insert(ci);
                }
            }
        }
        rels.push((r, rb.arity, rb.name.clone(), reps));
    }
    match order {
        // Java: by arity, then relation name
        0 => rels.sort_by(|a, b| a.1.cmp(&b.1).then_with(|| a.2.cmp(&b.2))),
        // portfolio alternatives: by arity then declaration order, or declaration order only
        1 => rels.sort_by(|a, b| a.1.cmp(&b.1)),
        _ => {}
    }
    for (ci, cl) in classes.iter().enumerate() {
        for w in cl.windows(2) {
            let (prev, cur) = (w[0], w[1]);
            let swap = |t: &[u32]| -> Vec<u32> {
                t.iter().map(|&x| if x == prev { cur } else if x == cur { prev } else { x }).collect()
            };
            let mut orig: Vec<BoolVal> = Vec::new();
            let mut perm: Vec<BoolVal> = Vec::new();
            for (r, _, _, reps) in &rels {
                if orig.len() >= pred_length {
                    break;
                }
                if !reps.contains(&ci) {
                    continue;
                }
                let m = &tr.rels[*r];
                for (t, v) in &m.entries {
                    if *v == BoolVal::FALSE {
                        continue;
                    }
                    let pt = swap(t);
                    if pt == *t {
                        continue;
                    }
                    let pv = m.get(&pt);
                    if orig.iter().zip(perm.iter()).any(|(o, p)| *o == pv && *p == *v) {
                        continue;
                    }
                    orig.push(*v);
                    perm.push(pv);
                }
            }
            // leq: for every i, (all earlier pairs equal) => (orig[i] => perm[i])
            let mut parts = Vec::new();
            let mut prev_eq = BoolVal::TRUE;
            for i in 0..orig.len() {
                let imp = tr.f.implies(orig[i], perm[i]);
                parts.push(tr.f.implies(prev_eq, imp));
                let eq = tr.f.iff(orig[i], perm[i]);
                prev_eq = tr.f.and2(prev_eq, eq);
            }
            let leq = tr.f.and(&parts);
            tr.f.assert_true(leq);
        }
    }
}

/// The result of solving one bounded problem.
#[derive(Debug, Clone)]
pub struct Solution {
    /// `Some(true)` SAT, `Some(false)` UNSAT, `None` unknown.
    pub sat: Option<bool>,
    pub instance: Option<Instance>,
    pub primary_vars: usize,
    pub vars: u32,
    pub clauses: u64,
}

/// Translates `formula` under `bounds`, solves with the default SAT backend and decodes the model.
pub fn solve(bounds: &Bounds, formula: &Formula) -> Result<Solution, String> {
    // 1. Java's symmetry-breaking predicate with a short budget: most commands finish here.
    {
        let mut sat = BatSat::configured(false, 0.0, 0, Some(true));
        sat.set_conflict_limit(Some(6_000));
        sat.set_time_limit(Some(std::time::Duration::from_millis(200)));
        let sol = solve_ordered(bounds, formula, sat, 0)?;
        if sol.sat.is_some() {
            return Ok(sol);
        }
    }
    // 2. SAT search time is heavy-tailed in the symmetry-breaking predicate and the restart schedule (it helps UNSAT
    //    proofs but can make satisfiable puzzles much harder), so race a few equally sound configurations; the
    //    first answer wins. With one core the configurations run one after another instead.
    // (symmetry-breaking order, luby restarts, random-decision frequency, seed, initial polarity)
    const CONFIGS: [(u8, bool, f64, u32, Option<bool>); 8] = [
        (0, false, 0.0, 0, Some(true)),
        (NO_SBP, false, 0.0, 0, None),
        (0, true, 0.0, 0, None),
        (1, true, 0.0, 0, Some(true)),
        (0, false, 0.0, 0, None),
        (1, false, 0.0, 0, None),
        (0, false, 0.01, 7, None),
        (NO_SBP, true, 0.0, 0, Some(true)),
    ];
    let cores = std::thread::available_parallelism().map_or(1, |n| n.get());
    if cores < 2 {
        for (order, luby) in [(NO_SBP, false), (0, false)] {
            let mut sat = BatSat::with_luby(luby);
            if order == NO_SBP {
                sat.set_time_limit(Some(std::time::Duration::from_millis(1_000)));
            }
            let sol = solve_ordered(bounds, formula, sat, order)?;
            if sol.sat.is_some() || order != NO_SBP {
                return Ok(sol);
            }
        }
        unreachable!("the last attempt is unlimited");
    }
    // Debug knob: KSAT_CONFIGS=3,5 races only the listed configurations.
    let selected: Vec<usize> = match std::env::var("KSAT_CONFIGS") {
        Ok(v) => v.split(',').filter_map(|x| x.trim().parse().ok()).filter(|i| *i < CONFIGS.len()).collect(),
        Err(_) => (0..CONFIGS.len().min(cores.max(2)).min(4)).collect(),
    };
    let stop = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let (tx, rx) = std::sync::mpsc::channel::<Result<Solution, String>>();
    std::thread::scope(|scope| {
        for &(order, luby, rnd, seed, pol) in selected.iter().map(|i| &CONFIGS[*i]) {
            let tx = tx.clone();
            let stop = stop.clone();
            scope.spawn(move || {
                let mut sat = BatSat::configured(luby, rnd, seed, pol);
                sat.set_stop_flag(stop);
                let r = solve_ordered(bounds, formula, sat, order);
                let _ = tx.send(r);
            });
        }
        drop(tx);
        let mut answer: Option<Result<Solution, String>> = None;
        for r in rx.iter() {
            let done = match &r {
                Ok(sol) => sol.sat.is_some(),
                Err(_) => true,
            };
            if done && answer.is_none() {
                answer = Some(r);
                stop.store(true, std::sync::atomic::Ordering::Relaxed);
            }
        }
        answer.unwrap_or_else(|| Err("no solver configuration finished".to_string()))
    })
}

pub fn solve_with<S: SatSolver>(bounds: &Bounds, formula: &Formula, sat: S) -> Result<Solution, String> {
    solve_ordered(bounds, formula, sat, 0)
}

fn solve_ordered<S: SatSolver>(bounds: &Bounds, formula: &Formula, sat: S, order: u8) -> Result<Solution, String> {
    let mut tr = Translator::new(bounds, sat);
    let top = if std::env::var("KPROF").is_ok() {
        if let Formula::And(items) = formula {
            let mut vals = Vec::new();
            for (k, it) in items.iter().enumerate() {
                let t0 = std::time::Instant::now();
                let v = tr.formula(it)?;
                let dt = t0.elapsed();
                if dt.as_millis() > 20 {
                    eprintln!("conjunct {k}: {:?} {:.1800}", dt, format!("{it:?}"));
                }
                vals.push(v);
            }
            tr.f.and(&vals)
        } else {
            tr.formula(formula)?
        }
    } else {
        tr.formula(formula)?
    };
    tr.f.assert_true(top);
    add_symmetry_breaking(&mut tr, order);
    tr.f.finish();
    // NOTE: Kodkod numbers skolem relations before gate variables; branching on them first (`set_priority`) made
    // some hard UNSAT models (ceilingsAndFloors) 3x slower and others slightly faster, so it is not enabled.
    if std::env::var("KSAT_PRIO").is_ok() {
        let mut prio: Vec<u32> = (1..=tr.primary_vars_base()).collect();
        prio.extend(tr.skolem_vars.iter().copied());
        tr.f.sat.set_priority(&prio);
    }
    let primary_vars = tr.primary_vars;
    let vars = tr.f.sat.num_vars();
    let clauses = tr.f.sat.num_clauses();
    if tr.f.trivially_unsat {
        return Ok(Solution {
            sat: Some(false),
            instance: None,
            primary_vars,
            vars,
            clauses,
        });
    }
    let r = tr.f.sat.solve();
    let instance = if r == Some(true) {
        let mut inst = Instance::default();
        for (id, rb) in bounds.relations.iter().enumerate() {
            let m = &tr.rels[id];
            let mut ts = TupleSet::empty(rb.arity);
            for (t, v) in &m.entries {
                let val = match *v {
                    BoolVal::Const(b) => b,
                    BoolVal::Lit(l) => {
                        let x = tr.f.sat.value_of(l.unsigned_abs());
                        if l > 0 {
                            x
                        } else {
                            !x
                        }
                    }
                };
                if val {
                    ts.tuples.insert(t.clone());
                }
            }
            inst.relations.insert(rb.name.clone(), ts);
        }
        Some(inst)
    } else {
        None
    };
    Ok(Solution {
        sat: r,
        instance,
        primary_vars,
        vars: tr.f.sat.num_vars(),
        clauses: tr.f.sat.num_clauses(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Decl, Expr, Formula, Multiplicity, Quantifier};
    use crate::instance::{Bounds, TupleSet, Universe};

    /// Atoms a0..a{n-1}; relation `R` (binary, free) and `A` (unary, exactly {a0, a1}).
    fn bounds(n: u32) -> (Bounds, u32, u32) {
        let u = Universe::new((0..n).map(|i| format!("a{i}")).collect()).unwrap();
        let mut b = Bounds::new(u);
        let r = b.bound("R", TupleSet::empty(2), TupleSet::all(2, n)).unwrap();
        let a_exact = TupleSet::from_tuples(1, [vec![0], vec![1]]);
        let a = b.bound("A", a_exact.clone(), a_exact).unwrap();
        (b, r, a)
    }

    fn some(e: Expr) -> Formula {
        Formula::Multiplicity(Multiplicity::Some, e)
    }

    #[test]
    fn free_relation_is_sat_and_empty_relation_is_unsat() {
        let (b, r, _) = bounds(2);
        let sol = solve(&b, &some(Expr::Rel(r))).unwrap();
        assert_eq!(sol.sat, Some(true));
        assert!(!sol.instance.unwrap().relations["R"].is_empty());
        let unsat = Formula::And(vec![some(Expr::Rel(r)), Formula::Multiplicity(Multiplicity::No, Expr::Rel(r))]);
        assert_eq!(solve(&b, &unsat).unwrap().sat, Some(false));
    }

    #[test]
    fn lower_bounds_are_forced_and_decoded() {
        let u = Universe::new(vec!["x".into(), "y".into()]).unwrap();
        let mut b = Bounds::new(u);
        let lower = TupleSet::from_tuples(2, [vec![0, 1]]);
        let r = b.bound("R", lower, TupleSet::all(2, 2)).unwrap();
        let f = Formula::Subset(Expr::Rel(r), Expr::Rel(r));
        let sol = solve(&b, &f).unwrap();
        assert_eq!(sol.sat, Some(true));
        let inst = sol.instance.unwrap();
        assert!(inst.relations["R"].contains(&[0, 1]));
    }

    #[test]
    fn transitive_closure_of_a_chain() {
        // R = {(0,1),(1,2)} forced; (0,2) must be in ^R, so asserting it is SAT and (2,0) UNSAT.
        let u = Universe::new(vec!["a".into(), "b".into(), "c".into()]).unwrap();
        let mut b = Bounds::new(u);
        let exact = TupleSet::from_tuples(2, [vec![0, 1], vec![1, 2]]);
        let r = b.bound("R", exact.clone(), exact).unwrap();
        let closure = Expr::Closure(Box::new(Expr::Rel(r)));
        let has02 = Formula::Subset(Expr::Literal(TupleSet::from_tuples(2, [vec![0, 2]])), closure.clone());
        assert_eq!(solve(&b, &has02).unwrap().sat, Some(true));
        let has20 = Formula::Subset(Expr::Literal(TupleSet::from_tuples(2, [vec![2, 0]])), closure);
        assert_eq!(solve(&b, &has20).unwrap().sat, Some(false));
    }

    #[test]
    fn universal_quantifier_over_a_domain() {
        let (b, r, a) = bounds(2);
        // all x: A | some x.R  (every atom of A has a successor) is satisfiable.
        let x = 0;
        let body = some(Expr::join(Expr::Var(x), Expr::Rel(r)));
        let f = Formula::Quantified(
            Quantifier::All,
            vec![Decl { var: x, domain: Expr::Rel(a), disjoint: false, set: false }],
            Box::new(body),
        );
        assert_eq!(solve(&b, &f).unwrap().sat, Some(true));
        // ... but not together with "no R".
        let g = Formula::And(vec![f, Formula::Multiplicity(Multiplicity::No, Expr::Rel(r))]);
        assert_eq!(solve(&b, &g).unwrap().sat, Some(false));
    }

    #[test]
    fn existential_quantifier_and_comprehension_arity() {
        let (b, r, a) = bounds(3);
        let x = 0;
        let f = Formula::Quantified(
            Quantifier::Some,
            vec![Decl { var: x, domain: Expr::Rel(a), disjoint: false, set: false }],
            Box::new(Formula::Subset(Expr::Var(x), Expr::Rel(a))),
        );
        assert_eq!(solve(&b, &f).unwrap().sat, Some(true));
        let comp = Expr::Comprehension(
            vec![Decl { var: x, domain: Expr::Rel(a), disjoint: false, set: false }],
            Box::new(some(Expr::Var(x))),
        );
        let mut vars = std::collections::HashMap::new();
        let tr = Translator::new(&b, BatSat::new());
        assert_eq!(tr.static_arity(&comp, &mut vars).unwrap(), 1);
        let _ = r;
    }
}

#[cfg(test)]
mod one_arrow_tests {
    use super::*;
    use crate::ast::{Decl, Expr, Formula, Multiplicity, Quantifier};
    use crate::instance::{Bounds, TupleSet, Universe};

    /// States S (unary), styles A (unary), values V (unary); field F: S -> A -> one V (arity 3).
    /// "all s: S, a: A | one s.F.a" and "some s: S | some s.F" must be SAT.
    #[test]
    fn one_arrow_field_with_some_is_sat() {
        let names = ["s0", "s1", "a0", "a1", "v0", "v1"];
        let u = Universe::new(names.iter().map(|x| x.to_string()).collect()).unwrap();
        let mut b = Bounds::new(u);
        let st = b.bound("S", TupleSet::empty(1), TupleSet::from_tuples(1, [vec![0], vec![1]])).unwrap();
        let sty = b.bound("A", TupleSet::from_tuples(1, [vec![2], vec![3]]), TupleSet::from_tuples(1, [vec![2], vec![3]])).unwrap();
        let _val = b.bound("V", TupleSet::empty(1), TupleSet::from_tuples(1, [vec![4], vec![5]])).unwrap();
        let mut up = TupleSet::empty(3);
        for s in [0u32, 1] {
            for a in [2u32, 3] {
                for v in [4u32, 5] {
                    up.tuples.insert(vec![s, a, v]);
                }
            }
        }
        let f = b.bound("F", TupleSet::empty(3), up).unwrap();
        let (s, a) = (0, 1);
        let one_each = Formula::Quantified(
            Quantifier::All,
            vec![
                Decl { var: s, domain: Expr::Rel(st), disjoint: false, set: false },
                Decl { var: a, domain: Expr::Rel(sty), disjoint: false, set: false },
            ],
            Box::new(Formula::Multiplicity(
                Multiplicity::One,
                Expr::join(Expr::Var(a), Expr::join(Expr::Var(s), Expr::Rel(f))),
            )),
        );
        let some_f = Formula::Quantified(
            Quantifier::Some,
            vec![Decl { var: 2, domain: Expr::Rel(st), disjoint: false, set: false }],
            Box::new(Formula::Multiplicity(Multiplicity::Some, Expr::join(Expr::Var(2), Expr::Rel(f)))),
        );
        let sol = solve(&b, &Formula::And(vec![one_each, some_f])).unwrap();
        assert_eq!(sol.sat, Some(true));
    }
}
