//! Port of `kodkod/engine/bool/BooleanFactory` + `engine/fol2sat/Bool2CNFTranslator`.
//!
//! Gates are hash-consed on their inputs, so structurally equal formulas share one node, as in Kodkod's
//! `CBCFactory`. Kinds: AND, OR (n-ary), IFF and ITE (one gate each, like Kodkod's `IFF`/`ITE`).
//! The circuit is built first; [`BoolFactory::finish`] then encodes the asserted roots to CNF with
//! Plaisted–Greenbaum polarity: a gate used only positively gets the clauses that force its inputs, a gate
//! used only negatively gets the clauses that force its output, and both sets are emitted only when both
//! polarities occur. Constants are folded away, so no clause contains a constant.

use std::collections::HashMap;

use satsolver::SatSolver;

/// A boolean value of the circuit: a constant or a DIMACS literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoolVal {
    Const(bool),
    Lit(i32),
}

impl BoolVal {
    pub const TRUE: BoolVal = BoolVal::Const(true);
    pub const FALSE: BoolVal = BoolVal::Const(false);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum GateKind {
    And,
    Or,
    /// inputs `[a, b]` (sorted): `g <-> (a <-> b)`.
    Iff,
    /// inputs `[c, t, e]`: `g <-> (c ? t : e)`.
    Ite,
}

struct Gate {
    kind: GateKind,
    /// Non-constant inputs (sorted for AND/OR/IFF; `[c, t, e]` order for ITE).
    inputs: Vec<i32>,
    /// SAT variable of the gate output.
    var: i32,
    /// Which directions were already emitted: `g -> f(inputs)` (positive) and `f(inputs) -> g` (negative).
    pos_done: bool,
    neg_done: bool,
}

pub struct BoolFactory<S: SatSolver> {
    pub sat: S,
    gates: Vec<Gate>,
    by_key: HashMap<(GateKind, Vec<i32>), usize>,
    /// Gate index of every gate output variable.
    by_var: HashMap<i32, usize>,
    /// Literals that must be true (encoded by [`BoolFactory::finish`]).
    roots: Vec<i32>,
    /// Set when a constant made the problem trivially unsatisfiable.
    pub trivially_unsat: bool,
}

impl<S: SatSolver> BoolFactory<S> {
    pub fn new(sat: S) -> Self {
        BoolFactory {
            sat,
            gates: Vec::new(),
            by_key: HashMap::new(),
            by_var: HashMap::new(),
            roots: Vec::new(),
            trivially_unsat: false,
        }
    }

    /// Number of distinct gates built so far (diagnostics).
    pub fn gate_count(&self) -> usize {
        self.gates.len()
    }

    /// A fresh primary variable (no defining clauses).
    pub fn new_var(&mut self) -> BoolVal {
        self.sat.add_variables(1);
        BoolVal::Lit(self.sat.num_vars() as i32)
    }

    fn clause(&mut self, lits: &[i32]) {
        if !self.sat.add_clause(lits) {
            self.trivially_unsat = true;
        }
    }

    pub fn not(&self, a: BoolVal) -> BoolVal {
        match a {
            BoolVal::Const(b) => BoolVal::Const(!b),
            BoolVal::Lit(l) => BoolVal::Lit(-l),
        }
    }

    pub fn and(&mut self, items: &[BoolVal]) -> BoolVal {
        self.connective(GateKind::And, items)
    }

    pub fn or(&mut self, items: &[BoolVal]) -> BoolVal {
        self.connective(GateKind::Or, items)
    }

    pub fn and2(&mut self, a: BoolVal, b: BoolVal) -> BoolVal {
        self.and(&[a, b])
    }

    pub fn or2(&mut self, a: BoolVal, b: BoolVal) -> BoolVal {
        self.or(&[a, b])
    }

    pub fn implies(&mut self, a: BoolVal, b: BoolVal) -> BoolVal {
        let na = self.not(a);
        self.or2(na, b)
    }

    /// `a <-> b` as one gate (Kodkod `IFF`).
    pub fn iff(&mut self, a: BoolVal, b: BoolVal) -> BoolVal {
        match (a, b) {
            (BoolVal::Const(true), _) => b,
            (BoolVal::Const(false), _) => self.not(b),
            (_, BoolVal::Const(true)) => a,
            (_, BoolVal::Const(false)) => self.not(a),
            (BoolVal::Lit(x), BoolVal::Lit(y)) if x == y => BoolVal::TRUE,
            (BoolVal::Lit(x), BoolVal::Lit(y)) if x == -y => BoolVal::FALSE,
            (BoolVal::Lit(x), BoolVal::Lit(y)) => {
                let mut ins = vec![x, y];
                ins.sort_unstable();
                self.gate(GateKind::Iff, ins)
            }
        }
    }

    /// `c ? t : e` as one gate (Kodkod `ITE`), with the constant cases folded into AND/OR.
    pub fn ite(&mut self, c: BoolVal, t: BoolVal, e: BoolVal) -> BoolVal {
        match c {
            BoolVal::Const(true) => return t,
            BoolVal::Const(false) => return e,
            _ => {}
        }
        if t == e {
            return t;
        }
        match (t, e) {
            (BoolVal::Const(true), _) => self.or2(c, e),
            (BoolVal::Const(false), _) => {
                let nc = self.not(c);
                self.and2(nc, e)
            }
            (_, BoolVal::Const(true)) => {
                let nc = self.not(c);
                self.or2(nc, t)
            }
            (_, BoolVal::Const(false)) => self.and2(c, t),
            (BoolVal::Lit(tl), BoolVal::Lit(el)) => {
                let BoolVal::Lit(cl) = c else { unreachable!("constant condition folded above") };
                self.gate(GateKind::Ite, vec![cl, tl, el])
            }
        }
    }

    /// Requires the value to hold (encoded by [`BoolFactory::finish`]).
    pub fn assert_true(&mut self, b: BoolVal) {
        match b {
            BoolVal::Const(true) => {}
            BoolVal::Const(false) => self.trivially_unsat = true,
            BoolVal::Lit(l) => self.roots.push(l),
        }
    }

    /// Encodes every asserted root to CNF (polarity-aware, see the module docs).
    pub fn finish(&mut self) {
        let roots = std::mem::take(&mut self.roots);
        for r in roots {
            if self.trivially_unsat {
                break;
            }
            // The root itself must hold; a gate root also needs its defining clauses.
            self.clause(&[r]);
            self.encode(r, true);
        }
    }

    /// Emits the clauses needed for literal `lit` to hold (`pos`) or to be false (`!pos`).
    fn encode(&mut self, lit: i32, pos: bool) {
        let mut work = vec![(lit, pos)];
        while let Some((l, p)) = work.pop() {
            if self.trivially_unsat {
                return;
            }
            // A primary variable (not a gate output): its value is free, nothing to emit.
            let Some(&gi) = self.by_var.get(&l.abs()) else { continue };
            let gate_pos = if l > 0 { p } else { !p };
            let (kind, inputs, out, need_pos, need_neg) = {
                let g = &self.gates[gi];
                (
                    g.kind,
                    g.inputs.clone(),
                    g.var,
                    gate_pos && !g.pos_done,
                    !gate_pos && !g.neg_done,
                )
            };
            if !need_pos && !need_neg {
                continue;
            }
            {
                let g = &mut self.gates[gi];
                g.pos_done |= need_pos;
                g.neg_done |= need_neg;
            }
            match kind {
                GateKind::And => self.encode_and(out, &inputs, need_pos, need_neg, &mut work),
                GateKind::Or => self.encode_or(out, &inputs, need_pos, need_neg, &mut work),
                GateKind::Iff => self.encode_iff(out, &inputs, need_pos, need_neg, &mut work),
                GateKind::Ite => self.encode_ite(out, &inputs, need_pos, need_neg, &mut work),
            }
        }
    }

    fn encode_and(&mut self, g: i32, ins: &[i32], pos: bool, neg: bool, work: &mut Vec<(i32, bool)>) {
        if pos {
            // g -> l_i
            for &x in ins {
                self.clause(&[-g, x]);
                work.push((x, true));
            }
        }
        if neg {
            // l_1 & ... & l_n -> g
            let mut c: Vec<i32> = ins.iter().map(|&x| -x).collect();
            c.push(g);
            self.clause(&c);
            for &x in ins {
                work.push((x, false));
            }
        }
    }

    fn encode_or(&mut self, g: i32, ins: &[i32], pos: bool, neg: bool, work: &mut Vec<(i32, bool)>) {
        if pos {
            // g -> (l_1 | ... | l_n)
            let mut c = vec![-g];
            c.extend(ins.iter().copied());
            self.clause(&c);
            for &x in ins {
                work.push((x, true));
            }
        }
        if neg {
            // l_i -> g
            for &x in ins {
                self.clause(&[g, -x]);
                work.push((x, false));
            }
        }
    }

    fn encode_iff(&mut self, g: i32, ins: &[i32], pos: bool, neg: bool, work: &mut Vec<(i32, bool)>) {
        let (a, b) = (ins[0], ins[1]);
        if pos {
            // g -> (a <-> b)
            self.clause(&[-g, -a, b]);
            self.clause(&[-g, a, -b]);
        }
        if neg {
            // (a <-> b) -> g
            self.clause(&[g, a, b]);
            self.clause(&[g, -a, -b]);
        }
        // Both inputs appear in both polarities.
        for &x in ins {
            work.push((x, true));
            work.push((x, false));
        }
    }

    fn encode_ite(&mut self, g: i32, ins: &[i32], pos: bool, neg: bool, work: &mut Vec<(i32, bool)>) {
        let (c, t, e) = (ins[0], ins[1], ins[2]);
        if pos {
            // g -> (c ? t : e)
            self.clause(&[-g, -c, t]);
            self.clause(&[-g, c, e]);
        }
        if neg {
            // (c ? t : e) -> g
            self.clause(&[g, -c, -t]);
            self.clause(&[g, c, -e]);
        }
        for &x in ins {
            work.push((x, true));
            work.push((x, false));
        }
    }

    /// Output literal of the hash-consed gate `kind(inputs)`.
    fn gate(&mut self, kind: GateKind, inputs: Vec<i32>) -> BoolVal {
        if let Some(&g) = self.by_key.get(&(kind, inputs.clone())) {
            return BoolVal::Lit(self.gates[g].var);
        }
        let BoolVal::Lit(var) = self.new_var() else { unreachable!() };
        let idx = self.gates.len();
        self.gates.push(Gate {
            kind,
            inputs: inputs.clone(),
            var,
            pos_done: false,
            neg_done: false,
        });
        self.by_key.insert((kind, inputs), idx);
        self.by_var.insert(var, idx);
        BoolVal::Lit(var)
    }

    fn connective(&mut self, kind: GateKind, items: &[BoolVal]) -> BoolVal {
        // Identity / absorbing constants of AND (true, false) and OR (false, true).
        let (identity, absorbing) = match kind {
            GateKind::And => (true, false),
            _ => (false, true),
        };
        let mut lits: Vec<i32> = Vec::with_capacity(items.len());
        for it in items {
            match *it {
                BoolVal::Const(b) if b == identity => {}
                BoolVal::Const(b) if b == absorbing => return BoolVal::Const(absorbing),
                BoolVal::Const(_) => {}
                BoolVal::Lit(l) => lits.push(l),
            }
        }
        lits.sort_unstable();
        lits.dedup();
        // x and not x
        for w in lits.windows(2) {
            if w[0] == -w[1] {
                return BoolVal::Const(absorbing);
            }
        }
        match lits.len() {
            0 => BoolVal::Const(identity),
            1 => BoolVal::Lit(lits[0]),
            _ => self.gate(kind, lits),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use satsolver::BatSat;

    #[test]
    fn constants_fold_and_gates_are_shared() {
        let mut f = BoolFactory::new(BatSat::new());
        let a = f.new_var();
        let b = f.new_var();
        assert_eq!(f.and(&[a, BoolVal::TRUE]), a);
        assert_eq!(f.or(&[a, BoolVal::TRUE]), BoolVal::TRUE);
        assert_eq!(f.and(&[a, f.not(a)]), BoolVal::FALSE);
        let x = f.and2(a, b);
        let y = f.and2(b, a);
        assert_eq!(x, y, "hash-consed");
        assert_eq!(f.iff(a, a), BoolVal::TRUE);
        assert_eq!(f.ite(a, BoolVal::TRUE, BoolVal::FALSE), a);
    }

    #[test]
    fn sat_and_unsat_small_circuits() {
        // (a <-> b) and a and not b  is UNSAT.
        let mut f = BoolFactory::new(BatSat::new());
        let a = f.new_var();
        let b = f.new_var();
        let iff = f.iff(a, b);
        f.assert_true(iff);
        f.assert_true(a);
        let nb = f.not(b);
        f.assert_true(nb);
        f.finish();
        assert!(f.trivially_unsat || f.sat.solve() == Some(false));
    }

    #[test]
    fn ite_semantics() {
        // c & !t & (c ? t : e) is UNSAT.
        let mut f = BoolFactory::new(BatSat::new());
        let c = f.new_var();
        let t = f.new_var();
        let e = f.new_var();
        let r = f.ite(c, t, e);
        f.assert_true(c);
        let nt = f.not(t);
        f.assert_true(nt);
        f.assert_true(r);
        f.finish();
        assert!(f.trivially_unsat || f.sat.solve() == Some(false));
    }

    #[test]
    fn ite_negative_polarity_is_encoded() {
        // not(c ? t : e) with c and t true is UNSAT.
        let mut f = BoolFactory::new(BatSat::new());
        let c = f.new_var();
        let t = f.new_var();
        let e = f.new_var();
        let r = f.ite(c, t, e);
        let nr = f.not(r);
        f.assert_true(nr);
        f.assert_true(c);
        f.assert_true(t);
        f.finish();
        assert!(f.trivially_unsat || f.sat.solve() == Some(false));
    }

    #[test]
    fn negative_polarity_gates_are_encoded() {
        // not(a & b) with a and b forced true is UNSAT.
        let mut f = BoolFactory::new(BatSat::new());
        let a = f.new_var();
        let b = f.new_var();
        let ab = f.and2(a, b);
        let n = f.not(ab);
        f.assert_true(n);
        f.assert_true(a);
        f.assert_true(b);
        f.finish();
        assert!(f.trivially_unsat || f.sat.solve() == Some(false));
    }
}
