//! Port of `kodkod/engine/bool/BooleanFactory` + the Tseitin part of `engine/fol2sat/Bool2CNFTranslator`.
//!
//! Gates are hash-consed on their (sorted) inputs, so structurally equal formulas share one SAT
//! variable, as in Kodkod's `CBCFactory`. Each new gate is encoded at creation time with the
//! full Tseitin clauses; constants are folded away so no clause contains a constant.

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

pub struct BoolFactory<S: SatSolver> {
    pub sat: S,
    gates: HashMap<(GateKind, Vec<i32>), i32>,
    /// Set when a clause made the problem trivially unsatisfiable.
    pub trivially_unsat: bool,
}

impl<S: SatSolver> BoolFactory<S> {
    pub fn new(sat: S) -> Self {
        BoolFactory {
            sat,
            gates: HashMap::new(),
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

    /// Requires the value to hold (adds it as a unit clause).
    pub fn assert_true(&mut self, b: BoolVal) {
        match b {
            BoolVal::Const(true) => {}
            BoolVal::Const(false) => self.trivially_unsat = true,
            BoolVal::Lit(l) => self.clause(&[l]),
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
        if let Some(&g) = self.gates.get(&(kind, lits.clone())) {
            return BoolVal::Lit(g);
        }
        let g = self.new_var();
        let BoolVal::Lit(g) = g else { unreachable!() };
        match kind {
            // g <-> AND(l_i):  (-g | l_i) for each i, and (g | -l_1 | ... | -l_n)
            GateKind::And => {
                for &l in &lits {
                    self.clause(&[-g, l]);
                }
                let mut long: Vec<i32> = lits.iter().map(|&l| -l).collect();
                long.push(g);
                self.clause(&long);
            }
            // g <-> OR(l_i):  (g | -l_i) for each i, and (-g | l_1 | ... | l_n)
            GateKind::Or => {
                for &l in &lits {
                    self.clause(&[g, -l]);
                }
                let mut long = lits.clone();
                long.push(-g);
                self.clause(&long);
            }
        }
        self.gates.insert((kind, lits), g);
        BoolVal::Lit(g)
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
        assert!(f.trivially_unsat || f.sat.solve() == Some(false));
    }

    #[test]
    fn ite_semantics() {
        let mut f = BoolFactory::new(BatSat::new());
        let c = f.new_var();
        let t = f.new_var();
        let e = f.new_var();
        let r = f.ite(c, t, e);
        // r must equal t when c holds: assert c, not t, r  -> UNSAT
        f.assert_true(c);
        let nt = f.not(t);
        f.assert_true(nt);
        f.assert_true(r);
        assert!(f.trivially_unsat || f.sat.solve() == Some(false));
    }
}
