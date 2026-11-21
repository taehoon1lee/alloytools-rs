//! Port of `kodkod/engine/bool/BooleanFactory` + `engine/fol2sat/Bool2CNFTranslator`.
//!
//! Gates are hash-consed on their (sorted) inputs, so structurally equal formulas share one node, as in
//! Kodkod's `CBCFactory`. The circuit is built first; [`BoolFactory::finish`] then encodes the asserted
//! roots to CNF with Plaisted–Greenbaum polarity: a gate used only positively gets just the clauses
//! `g -> input`, a gate used only negatively gets `inputs -> g`, and both directions are emitted only
//! when both polarities occur. Constants are folded away, so no clause contains a constant.

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
}

struct Gate {
    kind: GateKind,
    /// Sorted, deduplicated, non-constant inputs.
    inputs: Vec<i32>,
    /// SAT variable of the gate output.
    var: i32,
    /// Which directions were already emitted: `g -> inputs` (positive) and `inputs -> g` (negative).
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

    pub fn iff(&mut self, a: BoolVal, b: BoolVal) -> BoolVal {
        let ab = self.implies(a, b);
        let ba = self.implies(b, a);
        self.and2(ab, ba)
    }

    /// `c ? t : e`.
    pub fn ite(&mut self, c: BoolVal, t: BoolVal, e: BoolVal) -> BoolVal {
        match c {
            BoolVal::Const(true) => t,
            BoolVal::Const(false) => e,
            _ if t == e => t,
            _ => {
                let nc = self.not(c);
                let x = self.and2(c, t);
                let y = self.and2(nc, e);
                self.or2(x, y)
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

    /// Emits the clauses needed for literal `lit` to be true (`pos`) or false (`!pos`) under its gate.
    fn encode(&mut self, lit: i32, pos: bool) {
        // Iterative worklist: (literal, polarity) pairs still to be encoded.
        let mut work = vec![(lit, pos)];
        while let Some((l, p)) = work.pop() {
            let var = l.abs();
            // A primary variable (not a gate output): its value is free, nothing to emit.
            let Some(&gi) = self.by_var.get(&var) else { continue };
            // literal polarity relative to the gate output
            let gate_pos = if l > 0 { p } else { !p };
            let (kind, inputs, var_out, need_pos, need_neg) = {
                let g = &self.gates[gi];
                let need_pos = gate_pos && !g.pos_done;
                let need_neg = !gate_pos && !g.neg_done;
                (g.kind, g.inputs.clone(), g.var, need_pos, need_neg)
            };
            if !need_pos && !need_neg {
                continue;
            }
            {
                let g = &mut self.gates[gi];
                if need_pos {
                    g.pos_done = true;
                }
                if need_neg {
                    g.neg_done = true;
                }
            }
            match kind {
                GateKind::And => {
                    if need_pos {
                        // g -> l_i
                        for &x in &inputs {
                            self.clause(&[-var_out, x]);
                            if self.trivially_unsat {
                                return;
                            }
                            work.push((x, true));
                        }
                    }
                    if need_neg {
                        // l_1 & ... & l_n -> g
                        let mut c: Vec<i32> = inputs.iter().map(|&x| -x).collect();
                        c.push(var_out);
                        self.clause(&c);
                        if self.trivially_unsat {
                            return;
                        }
                        for &x in &inputs {
                            work.push((x, false));
                        }
                    }
                }
                GateKind::Or => {
                    if need_pos {
                        // g -> (l_1 | ... | l_n)
                        let mut c = vec![-var_out];
                        c.extend(inputs.iter().copied());
                        self.clause(&c);
                        if self.trivially_unsat {
                            return;
                        }
                        for &x in &inputs {
                            work.push((x, true));
                        }
                    }
                    if need_neg {
                        // l_i -> g
                        for &x in &inputs {
                            self.clause(&[var_out, -x]);
                            if self.trivially_unsat {
                                return;
                            }
                            work.push((x, false));
                        }
                    }
                }
            }
        }
    }

    fn connective(&mut self, kind: GateKind, items: &[BoolVal]) -> BoolVal {
        // Identity / absorbing constants of AND (true, false) and OR (false, true).
        let (identity, absorbing) = match kind {
            GateKind::And => (true, false),
            GateKind::Or => (false, true),
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
            0 => return BoolVal::Const(identity),
            1 => return BoolVal::Lit(lits[0]),
            _ => {}
        }
        if let Some(&g) = self.by_key.get(&(kind, lits.clone())) {
            return BoolVal::Lit(self.gates[g].var);
        }
        let BoolVal::Lit(var) = self.new_var() else { unreachable!() };
        let idx = self.gates.len();
        self.gates.push(Gate {
            kind,
            inputs: lits.clone(),
            var,
            pos_done: false,
            neg_done: false,
        });
        self.by_key.insert((kind, lits), idx);
        self.by_var.insert(var, idx);
        BoolVal::Lit(var)
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
        // c & !t & r  with r = ite(c, t, e) is UNSAT.
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
    fn negative_polarity_gates_are_encoded() {
        // not(a & b) asserted, with a and b forced true: must be UNSAT.
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
