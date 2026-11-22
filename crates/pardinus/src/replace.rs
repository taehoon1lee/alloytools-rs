//! Port of `kodkod.ast.visitor.AbstractReplacer` as used by `Translator.inlinePredicates` and of
//! `kodkod.engine.fol2sat.Skolemizer` (skolemDepth >= 0, no translation logging).

use crate::annotate::{annotate, Annotated};
use crate::ast::*;
use crate::bool::Factory;
use crate::fol2bool::{Fol2Bool, Leaf};
use crate::instance::{Bounds, Options, TupleSet};
use std::collections::{HashMap, HashSet};

/// A skolemized existential: the skolem relation and the Alloy-level declaration it replaces.
#[derive(Clone, Debug)]
pub struct SkolemInfo {
    pub relation: N,
    pub var: N,
    pub decl: N,
}

enum Mode {
    Inline(HashSet<N>),
    Skolem,
}

pub struct Replacer<'a> {
    pub ast: &'a mut Ast,
    shared: HashSet<N>,
    cache: HashMap<N, Option<N>>,
    mode: Mode,
    // ---- Skolemizer state
    bounds: Option<&'a mut Bounds>,
    rep_env: Vec<(N, N)>,
    negated: bool,
    skolem_depth: i32,
    top_constraints: Vec<N>,
    pub skolems: Vec<SkolemInfo>,
    bitwidth: i32,
}

fn is_formula(n: &Node) -> bool {
    matches!(
        n,
        Node::ConstF(_)
            | Node::BinF(..)
            | Node::NaryF(..)
            | Node::Not(_)
            | Node::Quant(..)
            | Node::Cmp(..)
            | Node::Mult(..)
            | Node::ICmp(..)
            | Node::PAcyclic(_)
            | Node::PFunction(..)
            | Node::PTotal(..)
            | Node::UTempF(..)
            | Node::BTempF(..)
    )
}

impl<'a> Replacer<'a> {
    fn lookup(&self, n: N) -> Option<N> {
        self.cache.get(&n).copied().flatten()
    }
    fn cache(&mut self, n: N, r: N) -> N {
        match self.mode {
            Mode::Inline(_) => {
                if self.shared.contains(&n) {
                    self.cache.insert(n, Some(r));
                }
            }
            Mode::Skolem => {
                if self.cache.contains_key(&n) {
                    self.cache.insert(n, Some(r));
                }
            }
        }
        r
    }
    fn skolem(&self) -> bool {
        matches!(self.mode, Mode::Skolem)
    }

    // ------------------------------------------------------------------ decls

    fn visit_decl(&mut self, d: N) -> Result<N, String> {
        if let Some(r) = self.lookup(d) {
            return Ok(r);
        }
        let (var, m, e) = match self.ast.get(d) {
            Node::Decl(v, m, e) => (*v, *m, *e),
            _ => unreachable!(),
        };
        if self.skolem() {
            let old = self.skolem_depth;
            self.skolem_depth = -1;
            let ne = self.visit(e)?;
            self.skolem_depth = old;
            let ret = if ne == e { d } else { self.ast.declare(var, m, ne) };
            return Ok(self.cache(d, ret));
        }
        let nv = self.visit(var)?;
        let ne = self.visit(e)?;
        let ret = if nv == var && ne == e { d } else { self.ast.declare(nv, m, ne) };
        Ok(self.cache(d, ret))
    }

    /// `visit(Decls)` (the Skolemizer also binds each variable to itself in the replacement environment)
    fn visit_decls(&mut self, ds: N) -> Result<N, String> {
        let list = self.ast.decls_list(ds);
        if let Some(r) = self.lookup(ds) {
            if self.skolem() {
                for d in &list {
                    let v = self.decl_var(*d);
                    self.rep_env.push((v, v));
                }
            }
            return Ok(r);
        }
        let mut visited: Option<N> = None;
        let mut all_same = true;
        for d in &list {
            let nd = self.visit_decl(*d)?;
            if nd != *d {
                all_same = false;
            }
            visited = Some(match visited {
                None => nd,
                Some(v) => self.ast.decls_and(v, nd),
            });
            if self.skolem() {
                let v = self.decl_var(*d);
                self.rep_env.push((v, v));
            }
        }
        let ret = if all_same { ds } else { visited.unwrap() };
        Ok(self.cache(ds, ret))
    }

    /// `decls().accept(this)` from AbstractReplacer: runtime dispatch (a single Decl is visited as a Decl)
    fn visit_decls_dispatch(&mut self, ds: N) -> Result<N, String> {
        match self.ast.get(ds) {
            Node::Decl(..) => self.visit_decl(ds),
            _ => self.visit_decls(ds),
        }
    }

    fn decl_var(&self, d: N) -> N {
        match self.ast.get(d) {
            Node::Decl(v, _, _) => *v,
            _ => unreachable!(),
        }
    }

    // ------------------------------------------------------------------ generic replacement

    pub fn visit(&mut self, n: N) -> Result<N, String> {
        let node = self.ast.get(n).clone();
        match node {
            Node::Rel(_) => Ok(match self.lookup(n) {
                Some(r) => r,
                None => self.cache(n, n),
            }),
            Node::Var { .. } => {
                if self.skolem() {
                    return self.rep_env.iter().rev().find(|(v, _)| *v == n).map(|(_, e)| *e).ok_or_else(|| "Unbound variable".into());
                }
                if self.lookup(n).is_none() {
                    self.cache(n, n);
                }
                Ok(n)
            }
            Node::ConstE(_) | Node::ConstF(_) | Node::IConst(_) => {
                if self.lookup(n).is_none() {
                    self.cache(n, n);
                }
                Ok(n)
            }
            Node::NaryE(op, cs) => {
                if let Some(r) = self.lookup(n) {
                    return Ok(r);
                }
                let mut v = Vec::with_capacity(cs.len());
                let mut same = true;
                for c in &cs {
                    let x = self.visit(*c)?;
                    same &= x == *c;
                    v.push(x);
                }
                let ret = if same {
                    n
                } else {
                    match v.len() {
                        1 => v[0],
                        2 => self.ast.add(Node::BinE(op, v[0], v[1])),
                        _ => self.ast.add(Node::NaryE(op, v)),
                    }
                };
                Ok(self.cache(n, ret))
            }
            Node::NaryI(op, cs) => {
                if let Some(r) = self.lookup(n) {
                    return Ok(r);
                }
                let mut v = Vec::with_capacity(cs.len());
                let mut same = true;
                for c in &cs {
                    let x = self.visit(*c)?;
                    same &= x == *c;
                    v.push(x);
                }
                let ret = if same {
                    n
                } else {
                    match v.len() {
                        1 => v[0],
                        2 => self.ast.add(Node::BinI(op, v[0], v[1])),
                        _ => self.ast.add(Node::NaryI(op, v)),
                    }
                };
                Ok(self.cache(n, ret))
            }
            Node::BinE(op, l, r) => self.bin(n, l, r, |a, x, y| a.add(Node::BinE(op, x, y))),
            Node::BinI(op, l, r) => self.bin(n, l, r, |a, x, y| a.add(Node::BinI(op, x, y))),
            Node::UnE(op, e) => self.un(n, e, |a, x| a.add(Node::UnE(op, x))),
            Node::UnI(op, e) => self.un(n, e, |a, x| a.add(Node::UnI(op, x))),
            Node::I2E(op, e) => self.un(n, e, |a, x| a.add(Node::I2E(op, x))),
            Node::E2I(op, e) => self.un(n, e, |a, x| a.add(Node::E2I(op, x))),
            Node::TempE(op, e) => self.un(n, e, |a, x| a.add(Node::TempE(op, x))),
            Node::Compr(d, f) => {
                if let Some(r) = self.lookup(n) {
                    return Ok(r);
                }
                if self.skolem() {
                    let old = self.rep_env.len();
                    let nd = self.visit_decls(d)?;
                    let nf = self.visit(f)?;
                    let ret = if nd == d && nf == f { n } else { self.ast.comprehension(nd, nf) };
                    self.rep_env.truncate(old);
                    return Ok(self.cache(n, ret));
                }
                let nd = self.visit_decls_dispatch(d)?;
                let nf = self.visit(f)?;
                let ret = if nd == d && nf == f { n } else { self.ast.comprehension(nd, nf) };
                Ok(self.cache(n, ret))
            }
            Node::Sum(d, e) => {
                if let Some(r) = self.lookup(n) {
                    return Ok(r);
                }
                if self.skolem() {
                    let old = self.rep_env.len();
                    let nd = self.visit_decls(d)?;
                    let ne = self.visit(e)?;
                    let ret = if nd == d && ne == e { n } else { self.ast.add(Node::Sum(nd, ne)) };
                    self.rep_env.truncate(old);
                    return Ok(self.cache(n, ret));
                }
                let nd = self.visit_decls_dispatch(d)?;
                let ne = self.visit(e)?;
                let ret = if nd == d && ne == e { n } else { self.ast.add(Node::Sum(nd, ne)) };
                Ok(self.cache(n, ret))
            }
            Node::IfE(c, t, e) | Node::IfI(c, t, e) => {
                if let Some(r) = self.lookup(n) {
                    return Ok(r);
                }
                let is_expr = matches!(self.ast.get(n), Node::IfE(..));
                let nc = self.visit(c)?;
                let nt = self.visit(t)?;
                let ne = self.visit(e)?;
                let ret = if nc == c && nt == t && ne == e {
                    n
                } else if is_expr {
                    self.ast.add(Node::IfE(nc, nt, ne))
                } else {
                    self.ast.add(Node::IfI(nc, nt, ne))
                };
                Ok(self.cache(n, ret))
            }
            Node::Proj(e, cols) => {
                if let Some(r) = self.lookup(n) {
                    return Ok(r);
                }
                let ne = self.visit(e)?;
                let mut same = ne == e;
                let mut nc = Vec::new();
                for c in &cols {
                    let x = self.visit(*c)?;
                    same &= x == *c;
                    nc.push(x);
                }
                let ret = if same { n } else { self.ast.add(Node::Proj(ne, nc)) };
                Ok(self.cache(n, ret))
            }
            Node::ICmp(op, l, r) => self.depth_wrap(|s| s.bin(n, l, r, |a, x, y| a.add(Node::ICmp(op, x, y)))),
            Node::Cmp(op, l, r) => self.depth_wrap(|s| s.bin(n, l, r, |a, x, y| a.add(Node::Cmp(op, x, y)))),
            Node::Mult(m, e) => self.depth_wrap(|s| s.un(n, e, |a, x| a.add(Node::Mult(m, x)))),
            Node::Quant(q, d, f) => {
                if self.skolem() {
                    return self.skolem_quant(n, q, d, f);
                }
                if let Some(r) = self.lookup(n) {
                    return Ok(r);
                }
                let nd = self.visit_decls_dispatch(d)?;
                let nf = self.visit(f)?;
                let ret = if nd == d && nf == f { n } else { self.ast.quantify(q, nd, nf) };
                Ok(self.cache(n, ret))
            }
            Node::NaryF(op, cs) => {
                if let Some(r) = self.lookup(n) {
                    return Ok(r);
                }
                let old = self.skolem_depth;
                if self.skolem() {
                    match op {
                        FOp::And if self.negated => self.skolem_depth = -1,
                        FOp::Or if !self.negated => self.skolem_depth = -1,
                        _ => {}
                    }
                }
                let mut v = Vec::with_capacity(cs.len());
                let mut same = true;
                for c in &cs {
                    let x = self.visit(*c)?;
                    same &= x == *c;
                    v.push(x);
                }
                let ret = if same { n } else { self.ast.compose_f(op, &v) };
                self.skolem_depth = old;
                Ok(self.cache(n, ret))
            }
            Node::BinF(op, l, r) => {
                if let Some(x) = self.lookup(n) {
                    return Ok(x);
                }
                if !self.skolem() {
                    let nl = self.visit(l)?;
                    let nr = self.visit(r)?;
                    let ret = if nl == l && nr == r { n } else { self.ast.binf(nl, op, nr) };
                    return Ok(self.cache(n, ret));
                }
                let old = self.skolem_depth;
                if op == FOp::Iff || (self.negated && op == FOp::And) || (!self.negated && (op == FOp::Or || op == FOp::Implies)) {
                    self.skolem_depth = -1;
                }
                let (nl, nr);
                if self.negated && op == FOp::Implies {
                    self.negated = !self.negated;
                    nl = self.visit(l)?;
                    self.negated = !self.negated;
                    nr = self.visit(r)?;
                } else {
                    nl = self.visit(l)?;
                    nr = self.visit(r)?;
                }
                self.skolem_depth = old;
                let ret = if nl == l && nr == r { n } else { self.ast.binf(nl, op, nr) };
                Ok(self.cache(n, ret))
            }
            Node::Not(f) => {
                if let Some(r) = self.lookup(n) {
                    return Ok(r);
                }
                if self.skolem() {
                    self.negated = !self.negated;
                    let c = self.visit(f)?;
                    self.negated = !self.negated;
                    if c == f {
                        return Ok(self.cache(n, n));
                    }
                    let nn = self.ast.not(c);
                    return Ok(self.cache(n, nn));
                }
                let c = self.visit(f)?;
                let ret = if c == f { n } else { self.ast.not(c) };
                Ok(self.cache(n, ret))
            }
            Node::PAcyclic(_) | Node::PFunction(..) | Node::PTotal(..) => {
                if let Mode::Inline(ref tp) = self.mode {
                    if let Some(r) = self.lookup(n) {
                        return Ok(r);
                    }
                    let is_true = tp.contains(&n);
                    let rep = if is_true { self.ast.tru() } else { self.to_constraints(n) };
                    return Ok(self.cache(n, rep));
                }
                Err("relation predicates must be inlined before skolemization".into())
            }
            Node::UTempF(op, f) => {
                if let Some(r) = self.lookup(n) {
                    return Ok(r);
                }
                let old = self.skolem_depth;
                if self.skolem() {
                    self.skolem_depth = -1;
                }
                let c = self.visit(f)?;
                self.skolem_depth = old;
                let ret = if c == f { n } else { self.ast.add(Node::UTempF(op, c)) };
                Ok(self.cache(n, ret))
            }
            Node::BTempF(op, l, r) => {
                if let Some(x) = self.lookup(n) {
                    return Ok(x);
                }
                let old = self.skolem_depth;
                if self.skolem() {
                    self.skolem_depth = -1;
                }
                let nl = self.visit(l)?;
                let nr = self.visit(r)?;
                self.skolem_depth = old;
                let ret = if nl == l && nr == r { n } else { self.ast.add(Node::BTempF(op, nl, nr)) };
                Ok(self.cache(n, ret))
            }
            Node::Decl(..) => self.visit_decl(n),
            Node::Decls(_) => self.visit_decls(n),
        }
    }

    fn depth_wrap(&mut self, f: impl FnOnce(&mut Self) -> Result<N, String>) -> Result<N, String> {
        if !self.skolem() {
            return f(self);
        }
        let old = self.skolem_depth;
        self.skolem_depth = -1;
        let r = f(self);
        self.skolem_depth = old;
        r
    }

    fn bin(&mut self, n: N, l: N, r: N, mk: impl FnOnce(&mut Ast, N, N) -> N) -> Result<N, String> {
        if let Some(x) = self.lookup(n) {
            return Ok(x);
        }
        let nl = self.visit(l)?;
        let nr = self.visit(r)?;
        let ret = if nl == l && nr == r { n } else { mk(self.ast, nl, nr) };
        Ok(self.cache(n, ret))
    }

    fn un(&mut self, n: N, e: N, mk: impl FnOnce(&mut Ast, N) -> N) -> Result<N, String> {
        if let Some(x) = self.lookup(n) {
            return Ok(x);
        }
        let ne = self.visit(e)?;
        let ret = if ne == e { n } else { mk(self.ast, ne) };
        Ok(self.cache(n, ret))
    }

    /// `RelationPredicate.toConstraints()`
    fn to_constraints(&mut self, p: N) -> N {
        let a = &mut *self.ast;
        match a.get(p).clone() {
            Node::PAcyclic(r) => {
                let c = a.closure(r);
                let iden = a.iden();
                let i = a.intersection(c, iden);
                a.mult(Mult::No, i)
            }
            Node::PFunction(r, dom, tm, rng) => {
                let prod = a.product(dom, rng);
                let domain_c = a.in_(r, prod);
                let name = format!("v{}", a.rel_info(r).name);
                let v = a.var(&name, 1);
                let j = a.join(v, r);
                let m = a.mult(tm, j);
                let d = a.one_of(v, dom);
                let fun_c = a.quantify(Quant::All, d, m);
                a.binf(domain_c, FOp::And, fun_c)
            }
            Node::PTotal(r, ordered, first, last) => {
                let f1 = a.mult(Mult::One, first);
                let l1 = a.mult(Mult::One, last);
                let a1 = a.binf(f1, FOp::And, l1);
                let lin = a.in_(last, ordered);
                let f0 = a.binf(a1, FOp::And, lin);
                let rc = a.add(Node::UnE(EOp::ReflexiveClosure, r));
                let fj = a.join(first, rc);
                let f1c = a.eq(ordered, fj);
                let rf = a.join(r, first);
                let n1 = a.mult(Mult::No, rf);
                let lr = a.join(last, r);
                let n2 = a.mult(Mult::No, lr);
                let f2 = a.binf(n1, FOp::And, n2);
                let name = format!("e{}", a.rel_info(r).name);
                let e = a.var(&name, 1);
                let er = a.join(e, r);
                let one = a.mult(Mult::One, er);
                let diff = a.difference(ordered, last);
                let d = a.one_of(e, diff);
                let f3 = a.quantify(Quant::All, d, one);
                a.add(Node::NaryF(FOp::And, vec![f0, f1c, f2, f3]))
            }
            _ => unreachable!(),
        }
    }

    // ------------------------------------------------------------------ Skolemizer.visit(QuantifiedFormula)

    fn skolem_quant(&mut self, n: N, q: Quant, d: N, body: N) -> Result<N, String> {
        if let Some(r) = self.lookup(n) {
            return Ok(r);
        }
        let old_env = self.rep_env.len();
        let mut ret;
        if self.skolem_depth >= 0 && ((self.negated && q == Quant::All) || (!self.negated && q == Quant::Some)) {
            let mut range: Vec<N> = Vec::new();
            for decl in self.ast.decls_list(d) {
                let sk_decl = self.visit_decl(decl)?;
                let (sk_var, sk_mult, sk_expr) = match self.ast.get(sk_decl) {
                    Node::Decl(v, m, e) => (*v, *m, *e),
                    _ => unreachable!(),
                };
                let (vname, varity) = match self.ast.get(sk_var) {
                    Node::Var { name, arity } => (name.clone(), *arity),
                    _ => unreachable!(),
                };
                let skolem = self.ast.add(Node::Rel(RelInfo { name: format!("${vname}"), arity: varity, var: false, atom: false, skolem: true }));
                self.skolems.push(SkolemInfo { relation: skolem, var: sk_var, decl });
                // skolemExpr (no non-skolem decls at depth 0): bound the skolem by the decl's upper approximation
                let ub = self.upper_bound(sk_expr)?;
                let ts = TupleSet::new(varity, ub.cells.keys().copied().collect());
                self.bounds.as_mut().unwrap().bound_upper(skolem, ts);
                let inr = self.ast.in_(skolem, sk_expr);
                range.push(inr);
                let mult = match self.ast.get(decl) {
                    Node::Decl(_, m, _) => *m,
                    _ => sk_mult,
                };
                if mult != Mult::Set {
                    let m = self.ast.mult(mult, skolem);
                    range.push(m);
                }
                let dv = self.decl_var(decl);
                self.rep_env.push((dv, skolem));
            }
            let rc = self.ast.and_all(&range);
            let nb = self.visit(body)?;
            ret = self.ast.binf(rc, if self.negated { FOp::Implies } else { FOp::And }, nb);
        } else {
            let nd = self.visit_decls(d)?;
            let ndecls = self.ast.decls_list(nd).len() as i32;
            if self.skolem_depth >= ndecls {
                return Err("skolem depth > 0 is not supported by the exact pipeline".into());
            }
            let old = self.skolem_depth;
            self.skolem_depth = -1;
            let nb = self.visit(body)?;
            ret = if nd == d && nb == body { n } else { self.ast.quantify(q, nd, nb) };
            self.skolem_depth = old;
        }
        self.rep_env.truncate(old_env);
        if self.rep_env.is_empty() && !self.top_constraints.is_empty() {
            let tc = self.top_constraints.clone();
            let c = self.ast.and_all(&tc);
            ret = self.ast.binf(c, if self.negated { FOp::Implies } else { FOp::And }, ret);
        }
        Ok(self.cache(n, ret))
    }

    /// `Skolemizer.upperBound(expr, emptyEnv)`: FOL2Bool approximation over the upper bounds.
    fn upper_bound(&mut self, e: N) -> Result<crate::bool::Matrix, String> {
        let b = self.bounds.as_ref().unwrap();
        let leaf = Leaf::constant(b.universe_size(), b.upper.clone(), b.ints.clone());
        let ann = annotate(self.ast, e);
        let mut f = Factory::new(0, 3, self.bitwidth, false);
        let mut t = Fol2Bool::new(self.ast, &ann, &leaf, &mut f, true);
        match t.translate(e)? {
            crate::fol2bool::Val::M(m) => Ok(m),
            _ => Err("skolem bound of a non-expression".into()),
        }
    }
}

/// `Translator.inlinePredicates(annotated, truePreds)`
pub fn inline_predicates(ast: &mut Ast, ann: &Annotated, true_preds: &[N]) -> Result<N, String> {
    let mut r = Replacer {
        ast,
        shared: ann.shared.clone(),
        cache: HashMap::new(),
        mode: Mode::Inline(true_preds.iter().copied().collect()),
        bounds: None,
        rep_env: Vec::new(),
        negated: false,
        skolem_depth: -1,
        top_constraints: Vec::new(),
        skolems: Vec::new(),
        bitwidth: 4,
    };
    r.visit(ann.node)
}

/// `Skolemizer.skolemize(annotated, bounds, options)`; returns the new root and the skolems.
pub fn skolemize(ast: &mut Ast, ann: &Annotated, bounds: &mut Bounds, opt: &Options) -> Result<(N, Vec<SkolemInfo>), String> {
    // cache seeded with the shared nodes without free variables that are no quantified formulas
    let mut cache = HashMap::new();
    for &n in &ann.shared {
        let mut memo = HashMap::new();
        if !ann.has_free_vars(ast, n, &mut memo) && (!is_formula(ast.get(n)) || !ann.has_quantifier(ast, n)) {
            cache.insert(n, None);
        }
    }
    let mut r = Replacer {
        ast,
        shared: ann.shared.clone(),
        cache,
        mode: Mode::Skolem,
        bounds: Some(bounds),
        rep_env: Vec::new(),
        negated: false,
        skolem_depth: opt.skolem_depth,
        top_constraints: Vec::new(),
        skolems: Vec::new(),
        bitwidth: opt.bitwidth,
    };
    let root = r.visit(ann.node)?;
    Ok((root, r.skolems))
}
