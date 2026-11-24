//! Port of `kodkod.engine.ltl2fol` (`TemporalTranslator`, `TemporalBoundsExpander`, `LTL2FOLTranslator`, explicit
//! unrolls) and of `TemporalPardinusSolver` (trace lengths min..max, each expanded and solved with BatSat),
//! plus `TemporalInstance` (states and loop of the lasso).

use std::collections::HashMap;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::Instant;

use crate::ast::{Ast, ConstE, EOp, FOp, Mult, Node, Quant, RelInfo, TOp, N};
use crate::instance::{Bounds, Problem, TupleSet};
use crate::replace::SkolemInfo;
use satsolver::{BatSat, SatSolver};

/// The relations of the temporal encoding (static singletons in Java) and `TRACE = PREFIX + LAST->LOOP`.
#[derive(Clone, Copy)]
pub struct TRels {
    pub first: N,
    pub last: N,
    pub last_: N,
    pub state: N,
    pub prefix: N,
    pub loop_: N,
    pub unroll: N,
    pub trace: N,
}

fn rel(ast: &mut Ast, name: &str, arity: u32) -> N {
    ast.add(Node::Rel(RelInfo { name: name.to_string(), arity, var: false, atom: false, skolem: false }))
}

impl TRels {
    pub fn new(ast: &mut Ast) -> TRels {
        let state = rel(ast, "Time", 1);
        let first = rel(ast, "S/first", 1);
        let last = rel(ast, "S/last", 1);
        let prefix = rel(ast, "S/next", 2);
        let loop_ = rel(ast, "loop", 1);
        let last_ = rel(ast, "S/last_", 1);
        let unroll = rel(ast, "unroll_map", 2);
        let lp = ast.product(last, loop_);
        let trace = ast.union(prefix, lp);
        TRels { first, last, last_, state, prefix, loop_, unroll, trace }
    }
}

/// `TemporalTranslator.countHeight`: nesting depth of past operators, plus one.
pub fn count_height(ast: &Ast, n: N) -> i32 {
    fn h(ast: &Ast, n: N) -> i32 {
        match ast.get(n) {
            Node::UTempF(op, f) => i32::from(matches!(op, TOp::Once | TOp::Historically | TOp::Before)) + h(ast, *f),
            Node::BTempF(op, a, b) => i32::from(matches!(op, TOp::Since | TOp::Triggered)) + h(ast, *a).max(h(ast, *b)),
            Node::Decl(_, _, e) => h(ast, *e),
            Node::PFunction(_, d, _, r) => h(ast, *d).max(h(ast, *r)),
            Node::PAcyclic(_) | Node::PTotal(..) => 0,
            _ => crate::annotate::children(ast, n).into_iter().map(|c| h(ast, c)).max().unwrap_or(0),
        }
    }
    h(ast, n) + 1
}

fn is_temporal(ast: &Ast, n: N) -> bool {
    match ast.get(n) {
        Node::UTempF(..) | Node::BTempF(..) | Node::TempE(..) => true,
        Node::Rel(ri) => ri.var,
        _ => crate::annotate::children(ast, n).into_iter().any(|c| is_temporal(ast, c)),
    }
}

/// Atom index of `Time<i>_<j>` in the expanded universe (`expandUniverse`: unroll-major).
fn time_atom(steps: u32, i: u32, j: u32) -> u32 {
    j * steps + i
}

/// `TemporalBoundsExpander.expand(bounds, steps, unrolls)` with `ExplicitUnrolls`.
pub fn expand(bounds: &Bounds, steps: u32, unrolls: u32, tr: &TRels, exp: &HashMap<N, N>, arity: &dyn Fn(N) -> u32) -> Bounds {
    let nt = steps * unrolls;
    let n0 = bounds.atoms.len() as u32;
    let n = nt + n0;
    let mut atoms: Vec<String> = Vec::with_capacity(n as usize);
    for j in 0..unrolls {
        for i in 0..steps {
            atoms.push(format!("Time{i}_{j}"));
        }
    }
    atoms.extend(bounds.atoms.iter().cloned());
    let mut nb = Bounds { atoms, ..Default::default() };
    let t1 = |v: Vec<u32>| TupleSet::new(1, v);
    let pair = |a: u32, b: u32| a * n + b;
    nb.bound_exactly(tr.first, t1(vec![time_atom(steps, 0, 0)]));
    nb.bound_exactly(tr.last, t1(vec![time_atom(steps, steps - 1, unrolls - 1)]));
    nb.bound_exactly(tr.last_, t1(vec![time_atom(steps, steps - 1, 0)]));
    let all_times: Vec<u32> = (0..nt).collect();
    let first_unroll: Vec<u32> = (0..steps).collect();
    let mut state_lower = first_unroll.clone();
    for j in 0..unrolls {
        state_lower.push(time_atom(steps, steps - 1, j));
    }
    nb.bound(tr.state, t1(state_lower), t1(all_times));
    let loop_upper: Vec<u32> = (0..steps).map(|i| time_atom(steps, i, unrolls - 1)).collect();
    nb.bound(tr.loop_, t1(Vec::new()), t1(loop_upper));
    let mut pl = Vec::new();
    let mut pu = Vec::new();
    for i in 0..steps.saturating_sub(1) {
        pl.push(pair(time_atom(steps, i, 0), time_atom(steps, i + 1, 0)));
    }
    for j in 0..unrolls {
        for i in 0..steps.saturating_sub(1) {
            pu.push(pair(time_atom(steps, i, j), time_atom(steps, i + 1, j)));
        }
        if j + 1 < unrolls {
            for k in 0..steps {
                pu.push(pair(time_atom(steps, steps - 1, j), time_atom(steps, k, j + 1)));
            }
        }
    }
    nb.bound(tr.prefix, TupleSet::new(2, pl), TupleSet::new(2, pu));
    if unrolls > 1 {
        let mut um = Vec::new();
        for i in 0..steps {
            um.push(pair(time_atom(steps, i, 0), time_atom(steps, i, 0)));
            for j in 1..unrolls {
                um.push(pair(time_atom(steps, i, j), time_atom(steps, i, 0)));
            }
        }
        nb.bound_exactly(tr.unroll, TupleSet::new(2, um));
    }
    // old tuples: every atom shifts by `nt`, the base grows from n0 to n
    let conv = |t: &TupleSet| -> Vec<u32> {
        let ar = t.arity;
        t.idx
            .iter()
            .map(|&x| {
                let mut digits = vec![0u32; ar as usize];
                let mut y = x;
                for k in (0..ar as usize).rev() {
                    digits[k] = y % n0;
                    y /= n0;
                }
                digits.iter().fold(0u32, |acc, &d| acc * n + d + nt)
            })
            .collect()
    };
    for r in bounds.relations() {
        let lo = conv(&bounds.lower[&r]);
        let up = conv(&bounds.upper[&r]);
        if let Some(&e) = exp.get(&r) {
            let ar = arity(r);
            let with_time = |v: &[u32]| -> Vec<u32> {
                let mut o = Vec::with_capacity(v.len() * steps as usize);
                for &x in v {
                    for &t in &first_unroll {
                        o.push(x * n + t);
                    }
                }
                o
            };
            nb.bound(e, TupleSet::new(ar + 1, with_time(&lo)), TupleSet::new(ar + 1, with_time(&up)));
        } else {
            let ar = arity(r);
            nb.bound(r, TupleSet::new(ar, lo), TupleSet::new(ar, up));
        }
    }
    for (&i, t) in &bounds.ints {
        nb.ints.insert(i, TupleSet::new(1, conv(t)));
    }
    nb.state = Some(tr.state);
    nb
}

/// `LTL2FOLTranslator` (an `AbstractReplacer` without caching: unchanged subtrees keep their identity).
struct Ltl2Fol<'a> {
    ast: &'a mut Ast,
    tr: TRels,
    exp: &'a HashMap<N, N>,
    has_past: bool,
    ops: Vec<TOp>,
    vars: Vec<N>,
    nvars: usize,
}

impl Ltl2Fol<'_> {
    fn cur(&self) -> N {
        *self.vars.last().expect("state variable")
    }
    fn prev(&self) -> N {
        self.vars[self.vars.len() - 2]
    }
    fn op(&self) -> TOp {
        *self.ops.last().expect("operator")
    }
    fn push_var(&mut self) {
        if self.vars.is_empty() {
            self.vars.push(self.tr.first);
            return;
        }
        let v = match self.op() {
            TOp::After | TOp::Prime => {
                let c = self.cur();
                self.ast.join(c, self.tr.trace)
            }
            TOp::Before => {
                let c = self.cur();
                let t = self.ast.transpose(self.tr.prefix);
                self.ast.join(c, t)
            }
            _ => {
                let v = self.ast.var(&format!("t{}", self.nvars), 1);
                self.nvars += 1;
                v
            }
        };
        self.vars.push(v);
    }
    fn rclosure(&mut self, e: N) -> N {
        self.ast.add(Node::UnE(EOp::ReflexiveClosure, e))
    }
    fn forall(&mut self, f: N, v: N, dom: N) -> N {
        let d = self.ast.one_of(v, dom);
        self.ast.quantify(Quant::All, d, f)
    }
    fn forsome(&mut self, f: N, v: N, dom: N) -> N {
        let d = self.ast.one_of(v, dom);
        self.ast.quantify(Quant::Some, d, f)
    }
    fn prefix_t(&mut self) -> N {
        self.ast.transpose(self.tr.prefix)
    }

    fn quantifier(&mut self, op: TOp, e: N) -> N {
        let s0 = self.prev();
        match op {
            TOp::Always | TOp::Eventually => {
                let s1 = self.cur();
                let rc = self.rclosure(self.tr.trace);
                let dom = self.ast.join(s0, rc);
                if op == TOp::Always {
                    self.forall(e, s1, dom)
                } else {
                    self.forsome(e, s1, dom)
                }
            }
            TOp::Historically | TOp::Once => {
                let s1 = self.cur();
                let pt = self.prefix_t();
                let rc = self.rclosure(pt);
                let dom = self.ast.join(s0, rc);
                if op == TOp::Historically {
                    self.forall(e, s1, dom)
                } else {
                    self.forsome(e, s1, dom)
                }
            }
            TOp::Before => {
                let v2 = self.cur();
                let s = self.ast.mult(Mult::Some, v2);
                self.ast.binf(s, FOp::And, e)
            }
            _ => e,
        }
    }

    fn up_to(&mut self, t1: N, t2: N, inc2: bool) -> N {
        let rc = self.rclosure(self.tr.prefix);
        let jr = self.ast.join(t1, rc);
        let c = self.ast.in_(t2, jr);
        let exp1 = self.rclosure(self.tr.prefix);
        let exp2 = self.ast.closure(self.tr.prefix);
        let exp11 = self.rclosure(self.tr.trace);
        let exp12 = self.ast.closure(self.tr.trace);
        let a = self.ast.join(t1, exp1);
        let e2t = self.ast.transpose(exp2);
        let b = self.ast.join(t2, e2t);
        let e1 = self.ast.intersection(a, b);
        let a = self.ast.join(t1, exp11);
        let e12t = self.ast.transpose(exp12);
        let b = self.ast.join(t2, e12t);
        let e21 = self.ast.intersection(a, b);
        let a = self.ast.join(t2, exp1);
        let e2t2 = self.ast.transpose(exp2);
        let b = self.ast.join(t1, e2t2);
        let e22 = self.ast.intersection(a, b);
        let e2 = self.ast.difference(e21, e22);
        let mut e = self.ast.add(Node::IfE(c, e1, e2));
        if inc2 {
            e = self.ast.union(e, t2);
        }
        e
    }

    fn down_to(&mut self, t1: N, t2: N, inc2: bool) -> N {
        let exp1 = self.rclosure(self.tr.prefix);
        let exp2 = self.ast.closure(self.tr.prefix);
        let e1t = self.ast.transpose(exp1);
        let a = self.ast.join(t1, e1t);
        let b = self.ast.join(t2, exp2);
        let mut e = self.ast.intersection(a, b);
        if inc2 {
            e = self.ast.union(e, t2);
        }
        e
    }

    fn visit(&mut self, n: N) -> Result<N, String> {
        let node = self.ast.get(n).clone();
        Ok(match node {
            Node::Rel(ri) => {
                if ri.var {
                    let e = *self.exp.get(&n).ok_or("variable relation without expansion")?;
                    let c = self.cur();
                    if self.has_past {
                        let cu = self.ast.join(c, self.tr.unroll);
                        self.ast.join(e, cu)
                    } else {
                        self.ast.join(e, c)
                    }
                } else {
                    n
                }
            }
            Node::ConstE(k) => {
                let eu = if self.has_past { self.ast.join(self.tr.unroll, self.tr.state) } else { self.tr.state };
                match k {
                    ConstE::Univ => self.ast.difference(n, eu),
                    ConstE::Iden => {
                        let p = self.ast.product(eu, eu);
                        self.ast.difference(n, p)
                    }
                    _ => n,
                }
            }
            Node::Var { .. } | Node::ConstF(_) | Node::IConst(_) => n,
            Node::PAcyclic(_) | Node::PFunction(..) | Node::PTotal(..) => {
                if is_temporal(self.ast, n) {
                    return Err("relation predicate over variable relations".into());
                }
                n
            }
            Node::UTempF(op, f) => {
                self.ops.push(op);
                self.push_var();
                let e = self.visit(f)?;
                let rt = self.quantifier(op, e);
                self.ops.pop();
                self.vars.pop();
                rt
            }
            Node::TempE(op, x) => {
                self.ops.push(op);
                self.push_var();
                let rt = self.visit(x)?;
                self.ops.pop();
                self.vars.pop();
                rt
            }
            Node::BTempF(op, a, b) => {
                self.ops.push(op);
                self.push_var();
                let rt = match op {
                    TOp::Until | TOp::Since => {
                        let right = self.visit(b)?;
                        self.push_var();
                        let left = self.visit(a)?;
                        // getVariableUntil(true) = vars[-2], (false) = vars[-1]; getVariablePrevQuantUntil(false) = vars[-3]
                        let k = self.vars.len();
                        let (r, l, prev_l) = (self.vars[k - 2], self.vars[k - 1], self.vars[k - 3]);
                        let rng = if op == TOp::Until { self.up_to(prev_l, r, false) } else { self.down_to(prev_l, r, false) };
                        let nfleft = self.forall(left, l, rng);
                        let nfleft = self.ast.binf(right, FOp::And, nfleft);
                        let dom = if op == TOp::Until {
                            let rc = self.rclosure(self.tr.trace);
                            self.ast.join(prev_l, rc)
                        } else {
                            let pt = self.prefix_t();
                            let rc = self.rclosure(pt);
                            self.ast.join(prev_l, rc)
                        };
                        let rt = self.forsome(nfleft, r, dom);
                        self.vars.pop();
                        rt
                    }
                    TOp::Releases | TOp::Triggered => {
                        let right_always = self.visit(b)?;
                        self.push_var();
                        let left = self.visit(a)?;
                        self.push_var();
                        let right = self.visit(b)?;
                        let k = self.vars.len();
                        // getVariableRelease(true,false) = vars[-2], (false,false) = vars[-1], (false,true) = vars[-3];
                        // getVariablePrevQuantRelease(false,true) = vars[-4]
                        let (r, l, v, pq) = (self.vars[k - 2], self.vars[k - 1], self.vars[k - 3], self.vars[k - 4]);
                        let rt = if op == TOp::Releases {
                            let rc = self.rclosure(self.tr.trace);
                            let dom = self.ast.join(pq, rc);
                            let alw = self.forall(right_always, v, dom);
                            let rng = self.up_to(pq, r, true);
                            let nfleft = self.forall(right, l, rng);
                            let nfright = self.ast.binf(left, FOp::And, nfleft);
                            let rc = self.rclosure(self.tr.trace);
                            let dom = self.ast.join(pq, rc);
                            let nfright = self.forsome(nfright, r, dom);
                            self.ast.binf(alw, FOp::Or, nfright)
                        } else {
                            let pt = self.prefix_t();
                            let rc = self.rclosure(pt);
                            let dom = self.ast.join(pq, rc);
                            let alw = self.forall(right_always, v, dom);
                            let rng = self.down_to(pq, r, true);
                            let nfleft = self.forall(right, l, rng);
                            let nfright = self.ast.binf(left, FOp::And, nfleft);
                            let pt = self.prefix_t();
                            let rc = self.rclosure(pt);
                            let dom = self.ast.join(pq, rc);
                            let nfright = self.forsome(nfright, r, dom);
                            self.ast.binf(alw, FOp::Or, nfright)
                        };
                        self.vars.pop();
                        self.vars.pop();
                        rt
                    }
                    _ => return Err("unsupported binary temporal operator".into()),
                };
                self.vars.pop();
                self.ops.pop();
                rt
            }
            // AbstractReplacer: rebuild only when a child changed
            Node::BinE(op, a, b) => {
                let (x, y) = (self.visit(a)?, self.visit(b)?);
                if x == a && y == b {
                    n
                } else {
                    self.ast.add(Node::BinE(op, x, y))
                }
            }
            Node::UnE(op, a) => {
                let x = self.visit(a)?;
                if x == a {
                    n
                } else {
                    self.ast.add(Node::UnE(op, x))
                }
            }
            Node::NaryE(op, v) => {
                let mut out = Vec::with_capacity(v.len());
                for &c in &v {
                    out.push(self.visit(c)?);
                }
                if out == v {
                    n
                } else if out.len() == 2 {
                    self.ast.add(Node::BinE(op, out[0], out[1]))
                } else {
                    self.ast.add(Node::NaryE(op, out))
                }
            }
            Node::Compr(d, f) => {
                let (x, y) = (self.visit(d)?, self.visit(f)?);
                if x == d && y == f {
                    n
                } else {
                    self.ast.add(Node::Compr(x, y))
                }
            }
            Node::IfE(c, a, b) => {
                let (x, y, z) = (self.visit(c)?, self.visit(a)?, self.visit(b)?);
                if x == c && y == a && z == b {
                    n
                } else {
                    self.ast.add(Node::IfE(x, y, z))
                }
            }
            Node::Proj(e, cols) => {
                let x = self.visit(e)?;
                let mut out = Vec::with_capacity(cols.len());
                for &c in &cols {
                    out.push(self.visit(c)?);
                }
                if x == e && out == cols {
                    n
                } else {
                    self.ast.add(Node::Proj(x, out))
                }
            }
            Node::I2E(op, a) => {
                let x = self.visit(a)?;
                if x == a {
                    n
                } else {
                    self.ast.add(Node::I2E(op, x))
                }
            }
            Node::E2I(op, a) => {
                let x = self.visit(a)?;
                if x == a {
                    n
                } else {
                    self.ast.add(Node::E2I(op, x))
                }
            }
            Node::BinI(op, a, b) => {
                let (x, y) = (self.visit(a)?, self.visit(b)?);
                if x == a && y == b {
                    n
                } else {
                    self.ast.add(Node::BinI(op, x, y))
                }
            }
            Node::NaryI(op, v) => {
                let mut out = Vec::with_capacity(v.len());
                for &c in &v {
                    out.push(self.visit(c)?);
                }
                if out == v {
                    n
                } else if out.len() == 2 {
                    self.ast.add(Node::BinI(op, out[0], out[1]))
                } else {
                    self.ast.add(Node::NaryI(op, out))
                }
            }
            Node::UnI(op, a) => {
                let x = self.visit(a)?;
                if x == a {
                    n
                } else {
                    self.ast.add(Node::UnI(op, x))
                }
            }
            Node::Sum(d, e) => {
                let (x, y) = (self.visit(d)?, self.visit(e)?);
                if x == d && y == e {
                    n
                } else {
                    self.ast.add(Node::Sum(x, y))
                }
            }
            Node::IfI(c, a, b) => {
                let (x, y, z) = (self.visit(c)?, self.visit(a)?, self.visit(b)?);
                if x == c && y == a && z == b {
                    n
                } else {
                    self.ast.add(Node::IfI(x, y, z))
                }
            }
            Node::ICmp(op, a, b) => {
                let (x, y) = (self.visit(a)?, self.visit(b)?);
                if x == a && y == b {
                    n
                } else {
                    self.ast.add(Node::ICmp(op, x, y))
                }
            }
            Node::Cmp(op, a, b) => {
                let (x, y) = (self.visit(a)?, self.visit(b)?);
                if x == a && y == b {
                    n
                } else {
                    self.ast.add(Node::Cmp(op, x, y))
                }
            }
            Node::Mult(m, a) => {
                let x = self.visit(a)?;
                if x == a {
                    n
                } else {
                    self.ast.add(Node::Mult(m, x))
                }
            }
            Node::Quant(q, d, f) => {
                let (x, y) = (self.visit(d)?, self.visit(f)?);
                if x == d && y == f {
                    n
                } else {
                    self.ast.add(Node::Quant(q, x, y))
                }
            }
            Node::BinF(op, a, b) => {
                let (x, y) = (self.visit(a)?, self.visit(b)?);
                if x == a && y == b {
                    n
                } else {
                    self.ast.add(Node::BinF(op, x, y))
                }
            }
            Node::NaryF(op, v) => {
                let mut out = Vec::with_capacity(v.len());
                for &c in &v {
                    out.push(self.visit(c)?);
                }
                if out == v {
                    n
                } else {
                    self.ast.compose_f(op, &out)
                }
            }
            Node::Not(a) => {
                let x = self.visit(a)?;
                if x == a {
                    n
                } else {
                    self.ast.not(x)
                }
            }
            Node::Decl(v, m, e) => {
                let x = self.visit(v)?;
                let y = self.visit(e)?;
                if x == v && y == e {
                    n
                } else {
                    self.ast.declare(x, m, y)
                }
            }
            Node::Decls(v) => {
                let mut acc: Option<N> = None;
                let mut same = true;
                for &d in &v {
                    let x = self.visit(d)?;
                    if x != d {
                        same = false;
                    }
                    acc = Some(match acc {
                        None => x,
                        Some(a) => self.ast.decls_and(a, x),
                    });
                }
                if same {
                    n
                } else {
                    acc.unwrap_or(n)
                }
            }
        })
    }
}

/// `LTL2FOLTranslator.translate(form, 0, has_past, log)`: the trace axioms and the formula at the first state.
pub fn ltl2fol(ast: &mut Ast, tr: TRels, exp: &HashMap<N, N>, form: N, has_past: bool) -> Result<N, String> {
    let v = ast.var("v", 1);
    // v.join(PREFIX).one() forAll v: STATE - LAST
    let j = ast.join(v, tr.prefix);
    let one = ast.mult(Mult::One, j);
    let dom = ast.difference(tr.state, tr.last);
    let d = ast.one_of(v, dom);
    let o1 = ast.quantify(Quant::All, d, one);
    let j = ast.join(tr.prefix, v);
    let one = ast.mult(Mult::One, j);
    let dom = ast.difference(tr.state, tr.first);
    let d = ast.one_of(v, dom);
    let o2 = ast.quantify(Quant::All, d, one);
    let rc = ast.add(Node::UnE(EOp::ReflexiveClosure, tr.prefix));
    let fr = ast.join(tr.first, rc);
    let mut o3 = ast.eq(fr, tr.state);
    let ss = ast.product(tr.state, tr.state);
    let o4 = ast.in_(tr.prefix, ss);
    if has_past {
        let v1 = ast.var("v1", 1);
        let a = ast.join(v, tr.unroll);
        let b = ast.join(v1, tr.unroll);
        let ab = ast.eq(a, b);
        let vt = ast.join(v, tr.trace);
        let vtu = ast.join(vt, tr.unroll);
        let v1t = ast.join(v1, tr.trace);
        let v1tu = ast.join(v1t, tr.unroll);
        let cd = ast.eq(vtu, v1tu);
        let imp = ast.binf(ab, FOp::Implies, cd);
        let rc = ast.add(Node::UnE(EOp::ReflexiveClosure, tr.trace));
        let dom1 = ast.join(tr.last_, rc);
        let d1 = ast.one_of(v1, dom1);
        let q1 = ast.quantify(Quant::All, d1, imp);
        let rc = ast.add(Node::UnE(EOp::ReflexiveClosure, tr.trace));
        let dom = ast.join(tr.last_, rc);
        let d0 = ast.one_of(v, dom);
        let q = ast.quantify(Quant::All, d0, q1);
        o3 = ast.binf(o3, FOp::And, q);
    }
    let lp = ast.mult(Mult::One, tr.loop_);
    let f = ast.compose_f(FOp::And, &[o1, o2, o3, o4, lp]);
    let mut t = Ltl2Fol { ast, tr, exp, has_past, ops: Vec::new(), vars: Vec::new(), nvars: 0 };
    t.vars.push(tr.first); // pushVariable(state = 0)
    let tfrm = t.visit(form)?;
    let tru = ast.tru();
    Ok(ast.compose_f(FOp::And, &[f, tfrm, tru]))
}

/// First solution of a temporal problem (states of the lasso over the static universe).
pub struct TemporalSolution {
    pub sat: bool,
    /// number of states (trace length) and the loop state
    pub steps: u32,
    pub loop_state: u32,
    /// per state: value of every original relation (static universe)
    pub states: Vec<HashMap<N, TupleSet>>,
    /// skolem relations of the final translation (value over the static universe; static only)
    pub skolems: Vec<(SkolemInfo, TupleSet)>,
    pub primary_vars: i32,
    pub vars: i32,
    pub clauses: i64,
    pub translate_ms: f64,
    pub solve_ms: f64,
    /// with `record`: the CNF calls of every SAT attempt (dev comparison with Java's dumps)
    pub cnf_log: Vec<Vec<String>>,
}

struct RecordingBuf {
    buf: crate::cnf::ClauseBuffer,
    log: Vec<String>,
}
impl crate::cnf::CnfSink for RecordingBuf {
    fn num_vars(&self) -> i32 {
        self.buf.num_vars
    }
    fn add_variables(&mut self, n: i32) {
        self.log.push(format!("v {n}"));
        self.buf.add_variables(n);
    }
    fn add_clause(&mut self, lits: &[i32]) {
        let mut s = String::from("c");
        for x in lits {
            s.push(' ');
            s.push_str(&x.to_string());
        }
        self.log.push(s);
        self.buf.add_clause(lits);
    }
}

fn decode_temporal_solution(
    p_bounds: &Bounds,
    ast: &Ast,
    tr: &TRels,
    exp: &HashMap<N, N>,
    steps: u32,
    unrolls: u32,
    ep_bounds: &Bounds,
    t: &crate::translator::Translation,
    value: &dyn Fn(i32) -> bool,
    vars: i32,
    clauses: i64,
    translate_ms: f64,
    solve_ms: f64,
    cnf_log: Vec<Vec<String>>,
) -> Result<TemporalSolution, String> {
    let inst: HashMap<N, TupleSet> = t.interpret(value).into_iter().collect();
    let nt = steps * unrolls;
    let n = ep_bounds.atoms.len() as u32;
    let n0 = n - nt;
    let decode = |idx: u32, ar: u32| -> Vec<u32> {
        let mut d = vec![0u32; ar as usize];
        let mut y = idx;
        for k in (0..ar as usize).rev() {
            d[k] = y % n;
            y /= n;
        }
        d
    };
    let encode0 = |d: &[u32]| -> Option<u32> {
        let mut acc = 0u32;
        for &a in d {
            if a < nt {
                return None;
            }
            acc = acc * n0 + (a - nt);
        }
        Some(acc)
    };
    let loop_atom = inst.get(&tr.loop_).and_then(|ts| ts.idx.first().copied()).ok_or("no loop state")?;
    let last_atom = inst.get(&tr.last).and_then(|ts| ts.idx.first().copied()).ok_or("no last state")?;
    let end = last_atom % steps;
    let loop_state = loop_atom % steps;
    let mut states = Vec::new();
    for i in 0..=end {
        let ti = time_atom(steps, i, 0);
        let mut m = HashMap::new();
        for r in p_bounds.relations() {
            let ar = ast.rel_info(r).arity;
            let mut v = Vec::new();
            if let Some(&e) = exp.get(&r) {
                if let Some(ts) = inst.get(&e) {
                    for &x in &ts.idx {
                        let d = decode(x, ar + 1);
                        if d[ar as usize] == ti {
                            if let Some(y) = encode0(&d[..ar as usize]) {
                                v.push(y);
                            }
                        }
                    }
                }
            } else if let Some(ts) = inst.get(&r) {
                for &x in &ts.idx {
                    if let Some(y) = encode0(&decode(x, ar)) {
                        v.push(y);
                    }
                }
            }
            m.insert(r, TupleSet::new(ar, v));
        }
        states.push(m);
    }
    let mut skolems = Vec::new();
    for s in &t.skolems {
        let ar = ast.rel_info(s.relation).arity;
        let mut v = Vec::new();
        if let Some(ts) = inst.get(&s.relation) {
            for &x in &ts.idx {
                if let Some(y) = encode0(&decode(x, ar)) {
                    v.push(y);
                }
            }
        }
        skolems.push((s.clone(), TupleSet::new(ar, v)));
    }
    Ok(TemporalSolution {
        sat: true,
        steps: end + 1,
        loop_state,
        states,
        skolems,
        primary_vars: t.num_primary,
        vars,
        clauses,
        translate_ms,
        solve_ms,
        cnf_log,
    })
}

/// `TemporalPardinusSolver.solveAll(...).next()` with `BatSat` portfolio (or sequential `JavaOrder` when `record = true`).
pub fn solve(p: &mut Problem, stop: Option<Arc<AtomicBool>>, record: bool) -> Result<TemporalSolution, String> {
    let mut cnf_log: Vec<Vec<String>> = Vec::new();
    let opt = p.options.clone();
    let (min, max) = (opt.min_trace.max(1) as u32, opt.max_trace.max(1) as u32);
    let mut ast = std::mem::take(&mut p.ast);
    let tr = TRels::new(&mut ast);
    // VarRelation: every variable relation has a static expansion with one more (time) column
    let mut exp: HashMap<N, N> = HashMap::new();
    for r in p.bounds.relations() {
        let ri = ast.rel_info(r).clone();
        if ri.var {
            let e = rel(&mut ast, &ri.name, ri.arity + 1);
            exp.insert(r, e);
        }
    }
    let result = (|| -> Result<TemporalSolution, String> {
        let prep = |ast: &mut Ast, goal: N| -> Result<(N, Bounds, i32), String> {
            let mut b = p.bounds.clone();
            let resolved = crate::translator::resolve(ast, &mut b, opt.bitwidth)?;
            let tru = ast.tru();
            let symb = ast.binf(tru, FOp::And, resolved);
            let f = ast.binf(goal, FOp::And, symb);
            let depth = count_height(ast, f);
            Ok((f, b, depth))
        };
        let arity_of = |ast: &Ast, r: N| ast.rel_info(r).arity;

        if record {
            let mut steps = min;
            let (f0, b0, depth0) = prep(&mut ast, p.goal)?;
            let ext0 = ltl2fol(&mut ast, tr, &exp, f0, depth0 > 1)?;
            let mut first = Some((ext0, b0, depth0));
            let mut translate_ms = 0.0;
            let mut solve_ms = 0.0;
            loop {
                if stop.as_ref().map_or(false, |s| s.load(std::sync::atomic::Ordering::Relaxed)) {
                    return Err("solver interrupted".into());
                }
                if steps > max {
                    return Ok(TemporalSolution {
                        sat: false,
                        steps: max,
                        loop_state: 0,
                        states: Vec::new(),
                        skolems: Vec::new(),
                        primary_vars: 0,
                        vars: 0,
                        clauses: 0,
                        translate_ms,
                        solve_ms,
                        cnf_log: std::mem::take(&mut cnf_log),
                    });
                }
                let t0 = Instant::now();
                let (ext, b, depth) = match first.take() {
                    Some(x) => x,
                    None => {
                        let (f, b, depth) = prep(&mut ast, p.goal)?;
                        let ext = ltl2fol(&mut ast, tr, &exp, f, depth > 1)?;
                        (ext, b, depth)
                    }
                };
                let unrolls = depth.max(1) as u32;
                let eb = {
                    let a = &ast;
                    expand(&b, steps, unrolls, &tr, &exp, &|r| arity_of(a, r))
                };
                let mut ep = Problem { ast: std::mem::take(&mut ast), bounds: eb, options: opt.clone(), goal: ext };
                let mut rec = RecordingBuf { buf: crate::cnf::ClauseBuffer::new(), log: Vec::new() };
                let tres = crate::translator::translate_expanded(&mut ep, &mut rec);
                cnf_log.push(rec.log);
                translate_ms += t0.elapsed().as_secs_f64() * 1000.0;
                ast = std::mem::take(&mut ep.ast);
                let t = tres?;
                let t1 = Instant::now();
                let mut solver = BatSat::configured(false, 0.0, 0, Some(true));
                solver.set_binary_watches(true);
                if let Some(f) = &stop {
                    solver.set_stop_flag(f.clone());
                }
                let sat = match t.trivial {
                    Some(v) => v,
                    None => {
                        if !rec.buf.feed_to(&mut solver) {
                            false
                        } else {
                            let frozen: Vec<u32> = (1..=t.num_primary as u32).collect();
                            solver.set_simplify(&frozen);
                            solver.solve().ok_or("solver interrupted")?
                        }
                    }
                };
                solve_ms += t1.elapsed().as_secs_f64() * 1000.0;
                if !sat {
                    steps += 1;
                    continue;
                }
                let trivial = t.trivial.is_some();
                let value = |v: i32| !trivial && v > 0 && solver.value_of(v as u32);
                return decode_temporal_solution(
                    &p.bounds,
                    &ast,
                    &tr,
                    &exp,
                    steps,
                    unrolls,
                    &ep.bounds,
                    &t,
                    &value,
                    rec.buf.num_vars,
                    rec.buf.num_clauses,
                    translate_ms,
                    solve_ms,
                    std::mem::take(&mut cnf_log),
                );
            }
        }

        // Production path: portfolio + temporal max-length probe (after 2 UNSAT lengths, check max_trace).
        let ks: Vec<u32> = (min..=max).collect();
        let mut translate_ms = 0.0;
        let mut solve_ms = 0.0;
        let mut run_step = |steps: u32| -> Result<(u32, Bounds, crate::translator::Solved), String> {
            let t0 = Instant::now();
            let (f, b, depth) = prep(&mut ast, p.goal)?;
            let ext = ltl2fol(&mut ast, tr, &exp, f, depth > 1)?;
            let unrolls = depth.max(1) as u32;
            let eb = {
                let a = &ast;
                expand(&b, steps, unrolls, &tr, &exp, &|r| arity_of(a, r))
            };
            let prep_ms = t0.elapsed().as_secs_f64() * 1000.0;
            let mut ep = Problem { ast: std::mem::take(&mut ast), bounds: eb, options: opt.clone(), goal: ext };
            let res = crate::translator::solve_portfolio(&mut ep);
            ast = std::mem::take(&mut ep.ast);
            let solved = res?;
            translate_ms += prep_ms + solved.translate_ms;
            solve_ms += solved.solve_ms;
            Ok((unrolls, ep.bounds, solved))
        };

        let mut probe: Option<(u32, u32, Bounds, crate::translator::Solved)> = None;
        let mut probed = ks.len() <= 3 || std::env::var("KTRACE_ALL").is_ok();
        let mut last_stats = (0i32, 0i32, 0i64);
        for (n, &steps) in ks.iter().enumerate() {
            if stop.as_ref().map_or(false, |s| s.load(std::sync::atomic::Ordering::Relaxed)) {
                return Err("solver interrupted".into());
            }
            if !probed && n == 2 {
                probed = true;
                let max_k = ks[ks.len() - 1];
                let (unrolls, eb, solved) = run_step(max_k)?;
                last_stats = (solved.translation.num_primary, solved.vars, solved.clauses);
                if !solved.sat {
                    return Ok(TemporalSolution {
                        sat: false,
                        steps: max_k,
                        loop_state: 0,
                        states: Vec::new(),
                        skolems: Vec::new(),
                        primary_vars: last_stats.0,
                        vars: last_stats.1,
                        clauses: last_stats.2,
                        translate_ms,
                        solve_ms,
                        cnf_log: Vec::new(),
                    });
                }
                probe = Some((max_k, unrolls, eb, solved));
            }
            let (unrolls, eb, solved) = if n + 1 == ks.len() && probe.is_some() {
                let (_, u, b, s) = probe.take().unwrap();
                (u, b, s)
            } else {
                run_step(steps)?
            };
            last_stats = (solved.translation.num_primary, solved.vars, solved.clauses);
            if solved.sat {
                let trivial = solved.translation.trivial.is_some();
                let value = |v: i32| !trivial && v > 0 && *solved.model.get(v as usize).unwrap_or(&false);
                return decode_temporal_solution(
                    &p.bounds,
                    &ast,
                    &tr,
                    &exp,
                    steps,
                    unrolls,
                    &eb,
                    &solved.translation,
                    &value,
                    solved.vars,
                    solved.clauses,
                    translate_ms,
                    solve_ms,
                    Vec::new(),
                );
            }
        }
        Ok(TemporalSolution {
            sat: false,
            steps: max,
            loop_state: 0,
            states: Vec::new(),
            skolems: Vec::new(),
            primary_vars: last_stats.0,
            vars: last_stats.1,
            clauses: last_stats.2,
            translate_ms,
            solve_ms,
            cnf_log: Vec::new(),
        })
    })();
    p.ast = ast;
    result
}

/// Minimal-prefix / minimal-period canonical lasso formula (avoids counting unrolled duplicates across trace lengths).
fn canonical_lasso(ast: &mut Ast, k: usize, var_exps: &[N], t0: &[N], tlast: &[N], loop_rel: N) -> N {
    let eq_state = |ast: &mut Ast, i: usize, j: usize| -> N {
        let mut parts = Vec::with_capacity(var_exps.len());
        for &e in var_exps {
            let ei = ast.join(e, t0[i]);
            let ej = ast.join(e, t0[j]);
            parts.push(ast.eq(ei, ej));
        }
        ast.and_all(&parts)
    };
    let mut cases = Vec::with_capacity(k);
    for l in 0..k {
        let is_l = ast.in_(tlast[l], loop_rel);
        let mut conds = Vec::new();
        if l > 0 {
            let eq = eq_state(ast, l - 1, k - 1);
            conds.push(ast.not(eq));
        }
        let q = k - l;
        for q2 in 1..q {
            if q % q2 == 0 {
                let mut rep = Vec::with_capacity(k - q2 - l);
                for j in l..k - q2 {
                    rep.push(eq_state(ast, j, j + q2));
                }
                let rep_and = ast.and_all(&rep);
                conds.push(ast.not(rep_and));
            }
        }
        let rhs = ast.and_all(&conds);
        cases.push(ast.binf(is_l, FOp::Implies, rhs));
    }
    ast.and_all(&cases)
}

/// Temporal `--count` (Pardinus `next()` semantics: first solution fixes static relations, then distinct canonical
/// lassos are enumerated over `min_trace..=max_trace` up to `limit`).
pub fn count_solutions(p: &mut Problem, limit: u32) -> Result<(u32, bool), String> {
    let mut opt = p.options.clone();
    opt.symmetry = 0;
    let (min, max) = (opt.min_trace.max(1) as u32, opt.max_trace.max(1) as u32);
    let mut ast = std::mem::take(&mut p.ast);
    let tr = TRels::new(&mut ast);
    let mut exp: HashMap<N, N> = HashMap::new();
    let orig_rels = p.bounds.relations();
    for &r in &orig_rels {
        let ri = ast.rel_info(r).clone();
        if ri.var {
            let e = rel(&mut ast, &ri.name, ri.arity + 1);
            exp.insert(r, e);
        }
    }
    let result = (|| -> Result<(u32, bool), String> {
        let mut b0 = p.bounds.clone();
        let resolved = crate::translator::resolve(&mut ast, &mut b0, opt.bitwidth)?;
        let tru = ast.tru();
        let symb = ast.binf(tru, FOp::And, resolved);
        let f0 = ast.binf(p.goal, FOp::And, symb);
        let depth = count_height(&ast, f0);
        let ext0 = ltl2fol(&mut ast, tr, &exp, f0, depth > 1)?;
        let unrolls = depth.max(1) as u32;

        let static_rels: Vec<N> = orig_rels
            .iter()
            .copied()
            .filter(|r| !exp.contains_key(r) && b0.lower[r].len() < b0.upper[r].len())
            .collect();
        let var_exps: Vec<N> = orig_rels.iter().filter_map(|r| exp.get(r).copied()).collect();
        let arity_of = |a: &Ast, r: N| a.rel_info(r).arity;

        let mut statics: Option<Vec<(N, TupleSet)>> = None;
        let mut total = 0u32;

        for steps in min..=max {
            if statics.is_none() {
                let eb = {
                    let a = &ast;
                    expand(&b0, steps, unrolls, &tr, &exp, &|r| arity_of(a, r))
                };
                let mut ep = Problem { ast: std::mem::take(&mut ast), bounds: eb, options: opt.clone(), goal: ext0 };
                let inst_res = crate::translator::first_instance(&mut ep, &static_rels);
                ast = std::mem::take(&mut ep.ast);
                let Some(inst) = inst_res? else {
                    continue;
                };
                let nt = steps * unrolls;
                let n = ep.bounds.atoms.len() as u32;
                let n0 = n - nt;
                let decode = |idx: u32, ar: u32| -> Vec<u32> {
                    let mut d = vec![0u32; ar as usize];
                    let mut y = idx;
                    for k in (0..ar as usize).rev() {
                        d[k] = y % n;
                        y /= n;
                    }
                    d
                };
                let encode0 = |d: &[u32]| -> Option<u32> {
                    let mut acc = 0u32;
                    for &a in d {
                        if a < nt {
                            return None;
                        }
                        acc = acc * n0 + (a - nt);
                    }
                    Some(acc)
                };
                let mut pinned = Vec::new();
                for &r in &static_rels {
                    let ar = ast.rel_info(r).arity;
                    let mut v = Vec::new();
                    if let Some(ts) = inst.get(&r) {
                        for &x in &ts.idx {
                            if let Some(y) = encode0(&decode(x, ar)) {
                                v.push(y);
                            }
                        }
                    }
                    let ts0 = TupleSet::new(ar, v);
                    if std::env::var("KCOUNT").is_ok() {
                        eprintln!("static {:?} {}: {:?}", r, ast.rel_info(r).name, ts0.idx);
                    }
                    pinned.push((r, ts0));
                }
                statics = Some(pinned);
            }

            let mut b_pinned = b0.clone();
            for (r, ts) in statics.as_ref().unwrap() {
                b_pinned.bound_exactly(*r, ts.clone());
            }
            let mut eb = {
                let a = &ast;
                expand(&b_pinned, steps, unrolls, &tr, &exp, &|r| arity_of(a, r))
            };
            let k = steps as usize;
            let mut t0 = Vec::with_capacity(k);
            let mut tlast = Vec::with_capacity(k);
            for i in 0..steps {
                let r0 = rel(&mut ast, &format!("$ct0_{i}"), 1);
                eb.bound_exactly(r0, TupleSet::new(1, vec![time_atom(steps, i, 0)]));
                t0.push(r0);
                if unrolls == 1 {
                    tlast.push(r0);
                } else {
                    let rl = rel(&mut ast, &format!("$ctl_{i}"), 1);
                    eb.bound_exactly(rl, TupleSet::new(1, vec![time_atom(steps, i, unrolls - 1)]));
                    tlast.push(rl);
                }
            }
            let canon = canonical_lasso(&mut ast, k, &var_exps, &t0, &tlast, tr.loop_);
            let goal_k = ast.binf(ext0, FOp::And, canon);
            let mut proj = var_exps.clone();
            proj.push(tr.loop_);
            let mut ep = Problem { ast: std::mem::take(&mut ast), bounds: eb, options: opt.clone(), goal: goal_k };
            let count_res = crate::translator::count_projected(&mut ep, limit - total, Some(&proj));
            ast = std::mem::take(&mut ep.ast);
            let (c, capped) = count_res?;
            if std::env::var("KCOUNT").is_ok() {
                eprintln!("k={steps} count={c} capped={capped}");
            }
            total += c;
            if capped {
                return Ok((total, true));
            }
            if total >= limit {
                continue;
            }
        }
        Ok((total, false))
    })();
    p.ast = ast;
    result
}
