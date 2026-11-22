//! Port of `edu.mit.csail.sdg.translator.Simplifier` (partial-instance inference, `A4Options.inferPartialInstance`)
//! with `A4Solution.shrink` / `A4Solution.approximate`. Java swallows every exception inside a simplification step;
//! here such a step returns `None` and is skipped the same way.

use super::*;

/// a tuple set over the universe: (arity, sorted tuple indices)
type Ts = (u32, Vec<u32>);

impl<'a> Cx<'a> {
    /// `Simplifier.simplify`: false when the formulas are found unsatisfiable.
    pub(super) fn simplify(&mut self) -> bool {
        let fs = self.formulas.clone();
        for &f in &fs {
            if !self.simplify_eq(f) {
                return false;
            }
        }
        for &f in &fs {
            if !self.simplify_in_f(f) {
                return false;
            }
        }
        true
    }

    fn simplify_in_f(&mut self, form: N) -> bool {
        match self.ast.get(form).clone() {
            Node::UTempF(TOp::Always, f) => self.simplify_in_f(f),
            Node::NaryF(FOp::And, v) => {
                for x in v {
                    if !self.simplify_in_f(x) {
                        return false;
                    }
                }
                true
            }
            Node::BinF(FOp::And, l, r) => self.simplify_in_f(l) && self.simplify_in_f(r),
            Node::Cmp(CmpOp::Subset, l, r) => self.simplify_in(l, r).unwrap_or(true),
            Node::Cmp(CmpOp::Equals, l, r) => self.simplify_in(l, r).unwrap_or(true) && self.simplify_in(r, l).unwrap_or(true),
            _ => true,
        }
    }

    fn simplify_eq(&mut self, form: N) -> bool {
        match self.ast.get(form).clone() {
            // Java: an `always` conjunct is handed to simplify_in
            Node::UTempF(TOp::Always, f) => self.simplify_in_f(f),
            Node::NaryF(FOp::And, v) => {
                for x in v {
                    if !self.simplify_eq(x) {
                        return false;
                    }
                }
                true
            }
            Node::BinF(FOp::And, l, r) => self.simplify_eq(l) && self.simplify_eq(r),
            Node::Cmp(CmpOp::Equals, l, r) => {
                let _ = self.simplify_equal(l, r);
                true
            }
            _ => true,
        }
    }

    /// `Simplifier.condense`: `a.(a->b)` is `b` when `a` is exactly one tuple.
    fn condense(&self, mut x: N) -> N {
        while let Node::BinE(EOp::Join, l, r) = self.ast.get(x).clone() {
            if !matches!(self.ast.get(l), Node::Rel(_)) {
                break;
            }
            let (Ok(up), Ok(lo)) = (self.query(true, l), self.query(false, l)) else { return x };
            if up.len() != 1 || lo.len() != 1 {
                return x;
            }
            match self.ast.get(r).clone() {
                Node::BinE(EOp::Product, pl, pr) if pl == l => x = pr,
                Node::BinE(..) => break,
                _ => break,
            }
        }
        x
    }

    fn is_rel(&self, e: N) -> bool {
        matches!(self.ast.get(e), Node::Rel(_))
    }

    /// `A4Solution.shrink` (an inconsistent shrink is an exception in Java: `None`)
    fn shrink(&mut self, r: N, lo: &[u32], hi: &[u32]) -> Option<()> {
        let old_l = self.bounds.lower.get(&r)?.idx.clone();
        let old_u = self.bounds.upper.get(&r)?.idx.clone();
        let sub = |a: &[u32], b: &[u32]| a.iter().all(|x| b.binary_search(x).is_ok());
        if sub(hi, &old_u) && sub(lo, hi) && sub(&old_l, lo) {
            let ar = self.ast.arity(r);
            self.bounds.bound(r, ts(ar, lo.to_vec()), ts(ar, hi.to_vec()));
            Some(())
        } else {
            None
        }
    }

    /// `Simplifier.simplify_equal`: tightens the bounds of a relation equal to another expression.
    fn simplify_equal(&mut self, a: N, b: N) -> Option<()> {
        let a = self.condense(a);
        let b = self.condense(b);
        if !(self.is_rel(a) || self.is_rel(b)) {
            return Some(());
        }
        let mut a0 = self.query(false, a).ok()?;
        let mut a1 = self.query(true, a).ok()?;
        let mut b0 = self.query(false, b).ok()?;
        let mut b1 = self.query(true, b).ok()?;
        let sub = |x: &[u32], y: &[u32]| x.iter().all(|t| y.binary_search(t).is_ok());
        if self.is_rel(a) && a0.len() < b0.len() && sub(&a0, &b0) && sub(&b0, &a1) {
            a0 = b0.clone();
            self.shrink(a, &a0, &a1)?;
        }
        if self.is_rel(a) && a1.len() > b1.len() && sub(&a0, &b1) && sub(&b1, &a1) {
            a1 = b1.clone();
            self.shrink(a, &a0, &a1)?;
        }
        if self.is_rel(b) && b0.len() < a0.len() && sub(&b0, &a0) && sub(&a0, &b1) {
            b0 = a0.clone();
            self.shrink(b, &b0, &b1)?;
        }
        if self.is_rel(b) && b1.len() > a1.len() && sub(&b0, &a1) && sub(&a1, &b1) {
            b1 = a1.clone();
            self.shrink(b, &b0, &b1)?;
        }
        Some(())
    }

    /// `Simplifier.simplify_in(a, b)`: `Some(false)` when the upper bound of `a` falls below its lower bound.
    fn simplify_in(&mut self, a: N, b: N) -> Option<bool> {
        let a = self.condense(a);
        let b = self.condense(b);
        if !self.is_rel(a) {
            return Some(true);
        }
        let ub = self.query(true, a).ok()?;
        let lb = self.query(false, a).ok()?;
        let t = self.approximate(b)?;
        let t: Vec<u32> = t.1.into_iter().filter(|x| ub.binary_search(x).is_ok()).collect();
        if !lb.iter().all(|x| t.binary_search(x).is_ok()) {
            return Some(false);
        }
        if t.len() < ub.len() {
            self.shrink(a, &lb, &t)?;
        }
        Some(true)
    }

    /// `A4Solution.approximate`: the value of `e` when every relation equals its upper bound.
    fn approximate(&self, e: N) -> Option<Ts> {
        let n = self.bounds.universe_size();
        let pow = |k: u32| n.pow(k);
        Some(match self.ast.get(e).clone() {
            Node::Rel(_) => (self.ast.arity(e), self.query(true, e).ok()?),
            Node::ConstE(ConstE::None) => (1, Vec::new()),
            Node::ConstE(ConstE::Univ) => (1, (0..n).collect()),
            Node::ConstE(ConstE::Iden) => (2, (0..n).map(|i| i * n + i).collect()),
            Node::ConstE(ConstE::Ints) => (1, self.sigint.clone()),
            Node::BinE(op, l, r) => {
                let (al, x) = self.approximate(l)?;
                let (ar, y) = self.approximate(r)?;
                match op {
                    EOp::Union => (al, merge(&x, &y)),
                    EOp::Intersection => (al, x.into_iter().filter(|t| y.binary_search(t).is_ok()).collect()),
                    EOp::Difference => (al, x.into_iter().filter(|t| y.binary_search(t).is_err()).collect()),
                    EOp::Product => {
                        let m = pow(ar);
                        let mut v: Vec<u32> = x.iter().flat_map(|p| y.iter().map(move |q| p * m + q)).collect();
                        v.sort_unstable();
                        (al + ar, v)
                    }
                    EOp::Join => {
                        let (ml, mr) = (pow(ar - 1), n);
                        let mut v = Vec::new();
                        for &p in &x {
                            let last = p % n;
                            let head = p / n;
                            for &q in &y {
                                if q / pow(ar - 1) == last {
                                    v.push(head * ml + q % pow(ar - 1));
                                }
                            }
                        }
                        let _ = mr;
                        v.sort_unstable();
                        v.dedup();
                        (al + ar - 2, v)
                    }
                    EOp::Override => {
                        let m = pow(al - 1);
                        let dom: Vec<u32> = y.iter().map(|q| q / m).collect();
                        let mut v: Vec<u32> = x.into_iter().filter(|p| !dom.contains(&(p / m))).collect();
                        v.extend(y);
                        v.sort_unstable();
                        v.dedup();
                        (al, v)
                    }
                    _ => return None,
                }
            }
            Node::UnE(op, x) => {
                let (ax, v) = self.approximate(x)?;
                match op {
                    EOp::Transpose if ax == 2 => {
                        let mut t: Vec<u32> = v.iter().map(|p| (p % n) * n + p / n).collect();
                        t.sort_unstable();
                        (2, t)
                    }
                    EOp::Closure if ax == 2 => (2, closure(&v, n)),
                    EOp::ReflexiveClosure if ax == 2 => {
                        let iden: Vec<u32> = (0..n).map(|i| i * n + i).collect();
                        (2, merge(&closure(&v, n), &iden))
                    }
                    _ => return None,
                }
            }
            _ => return None,
        })
    }
}

fn merge(a: &[u32], b: &[u32]) -> Vec<u32> {
    let mut v: Vec<u32> = a.iter().chain(b.iter()).copied().collect();
    v.sort_unstable();
    v.dedup();
    v
}

fn closure(v: &[u32], n: u32) -> Vec<u32> {
    let mut cur: Vec<u32> = v.to_vec();
    loop {
        let mut next = cur.clone();
        for &p in &cur {
            for &q in v {
                if p % n == q / n {
                    next.push((p / n) * n + q % n);
                }
            }
        }
        next.sort_unstable();
        next.dedup();
        if next.len() == cur.len() {
            return next;
        }
        cur = next;
    }
}
