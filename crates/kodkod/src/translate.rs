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
    env: HashMap<VarId, BoolMatrix>,
    /// Number of primary variables (free upper-bound tuples).
    pub primary_vars: usize,
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
            env: HashMap::new(),
            primary_vars,
        }
    }

    fn n(&self) -> u32 {
        self.bounds.universe.size() as u32
    }

    /// Evaluates a relational expression.
    pub fn expr(&mut self, e: &Expr) -> Result<BoolMatrix, String> {
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
                let cond = self.formula(c)?;
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
                let body: Formula = (**body).clone();
                let mut key = Vec::new();
                let mut leaves = Vec::new();
                if decls.iter().any(|d| d.set) {
                    return Err("set declarations in comprehensions are not supported yet".into());
                }
                self.leaves(decls, 0, BoolVal::TRUE, &mut key, false, &mut leaves, &mut |t: &mut Self, g| {
                    let b = t.formula(&body)?;
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
            IntExpr::Neg(a) => {
                let a = self.int_expr(a)?;
                self.neg_bits(&a)
            }
        })
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
            return Err("join needs an expression of arity 2 or more".into());
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
            Expr::Var(v) => *vars.get(v).ok_or_else(|| format!("unbound variable {v}"))?,
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
                let ab = self.subset(&a, &b);
                let ba = self.subset(&b, &a);
                self.f.and2(ab, ba)
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
                let a = self.formula(a)?;
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
                let (a, b) = (self.formula(a)?, self.formula(b)?);
                self.f.implies(a, b)
            }
            Formula::Iff(a, b) => {
                let (a, b) = (self.formula(a)?, self.formula(b)?);
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
            Formula::Quantified(q, decls, body) => {
                // Duality for set declarations: all s ⊆ E. f  ==  not (some s ⊆ E. not f). The existential
                // side is solved with witness bits, so no subset enumeration is needed.
                if *q == Quantifier::All && decls.iter().any(|d| d.set) {
                    let dual = Formula::Quantified(
                        Quantifier::Some,
                        decls.clone(),
                        Box::new(Formula::Not(body.clone())),
                    );
                    return self.formula(&Formula::Not(Box::new(dual)));
                }
                let body = body.clone();
                let mut key = Vec::new();
                let mut leaves = Vec::new();
                let all = *q == Quantifier::All;
                self.leaves(decls, 0, BoolVal::TRUE, &mut key, all, &mut leaves, &mut |t: &mut Self, g| {
                    let b = t.formula(&body)?;
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
        let mut parts = Vec::new();
        for i in 0..vals.len() {
            for j in i + 1..vals.len() {
                let both = self.f.and2(vals[i], vals[j]);
                parts.push(self.f.not(both));
            }
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

fn same_arity(a: &BoolMatrix, b: &BoolMatrix, op: &str) -> Result<(), String> {
    if a.arity == b.arity {
        Ok(())
    } else {
        Err(format!("{op} of expressions with different arities ({} and {})", a.arity, b.arity))
    }
}

/// Interchangeable atom pairs: `(a, b)` such that swapping `a` and `b` maps every relation's lower and
/// upper bound onto itself (Kodkod's `SymmetryDetector`, restricted to transpositions). Atoms in
/// `ordered_atoms` are excluded.
pub fn symmetric_pairs(bounds: &Bounds) -> Vec<(u32, u32)> {
    let n = bounds.universe.size() as u32;
    // signature: degree of each atom in every relation's bounds (a cheap class key; verified below)
    let mut key: Vec<Vec<usize>> = vec![Vec::new(); n as usize];
    for rb in &bounds.relations {
        for a in 0..n {
            let lo = rb.lower.tuples.iter().filter(|t| t.contains(&a)).count();
            let up = rb.upper.tuples.iter().filter(|t| t.contains(&a)).count();
            key[a as usize].push(lo);
            key[a as usize].push(up);
        }
    }
    let mut groups: std::collections::BTreeMap<Vec<usize>, Vec<u32>> = std::collections::BTreeMap::new();
    for a in 0..n {
        if bounds.ordered_atoms.contains(&a) {
            continue;
        }
        groups.entry(key[a as usize].clone()).or_default().push(a);
    }
    let mut pairs = Vec::new();
    for atoms in groups.values() {
        for w in atoms.windows(2) {
            let (a, b) = (w[0], w[1]);
            let swap = |t: &Vec<u32>| -> Vec<u32> {
                t.iter()
                    .map(|&x| if x == a { b } else if x == b { a } else { x })
                    .collect()
            };
            let invariant = bounds.relations.iter().all(|rb| {
                let up: std::collections::BTreeSet<Vec<u32>> = rb.upper.tuples.iter().map(swap).collect();
                let lo: std::collections::BTreeSet<Vec<u32>> = rb.lower.tuples.iter().map(swap).collect();
                up == rb.upper.tuples && lo == rb.lower.tuples
            });
            if invariant {
                pairs.push((a, b));
            }
        }
    }
    pairs
}

/// Lex-leader symmetry breaking (Kodkod `SymmetryBreaker`): for every symmetric pair `(a, b)` the bit
/// vector of all relations is lexicographically at most its image under the swap of `a` and `b`.
/// Every orbit keeps its lex-smallest member, so satisfiability is unchanged.
fn add_symmetry_breaking<S: SatSolver>(tr: &mut Translator<'_, S>) {
    let bounds = tr.bounds;
    for (a, b) in symmetric_pairs(bounds) {
        let swap = |t: &[u32]| -> Vec<u32> {
            t.iter().map(|&x| if x == a { b } else if x == b { a } else { x }).collect()
        };
        let mut xs = Vec::new();
        let mut ys = Vec::new();
        for (r, rb) in bounds.relations.iter().enumerate() {
            let m = &tr.rels[r];
            for t in &rb.upper.tuples {
                xs.push(m.get(t));
                ys.push(m.get(&swap(t)));
            }
        }
        let leq = lex_leq(&mut tr.f, &xs, &ys);
        tr.f.assert_true(leq);
    }
}

/// `xs <=lex ys` as a circuit: `leq_i = (!x_i & y_i) | ((x_i <-> y_i) & leq_{i+1})`, `leq_n = true`.
fn lex_leq<S: SatSolver>(f: &mut BoolFactory<S>, xs: &[BoolVal], ys: &[BoolVal]) -> BoolVal {
    let mut acc = BoolVal::TRUE;
    for i in (0..xs.len()).rev() {
        let nx = f.not(xs[i]);
        let lt = f.and2(nx, ys[i]);
        let eq = f.iff(xs[i], ys[i]);
        let keep = f.and2(eq, acc);
        acc = f.or2(lt, keep);
    }
    acc
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
    solve_with(bounds, formula, BatSat::new())
}

pub fn solve_with<S: SatSolver>(bounds: &Bounds, formula: &Formula, sat: S) -> Result<Solution, String> {
    let mut tr = Translator::new(bounds, sat);
    let top = tr.formula(formula)?;
    tr.f.assert_true(top);
    add_symmetry_breaking(&mut tr);
    tr.f.finish();
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
