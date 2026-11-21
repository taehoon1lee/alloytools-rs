//! SAT solver interface. Port of `kodkod.engine.satlab.SATSolver`.
//!
//! Literals use the DIMACS convention exactly like Kodkod: variables are `1..=num_vars`,
//! a literal is `+v` or `-v` (i32). Kodkod's `Bool2CNFTranslator` produces such clauses.
//!
//! Backends:
//!   * [`BatSat`] — pure-Rust MiniSat-style CDCL (crate `batsat`). Default.
//!   Add your own CDCL here later if profiling shows the SAT backend is the bottleneck
//!   (the Java baseline uses SAT4J, a MiniSat-style CDCL in Java).

use batsat::{lbool, Lit, Solver, SolverInterface, Var};

pub trait SatSolver {
    /// Number of variables allocated so far.
    fn num_vars(&self) -> u32;
    /// Number of clauses added so far.
    fn num_clauses(&self) -> u64;
    /// Allocate `n` fresh variables (they become `num_vars()+1 ..= num_vars()+n`).
    fn add_variables(&mut self, n: u32);
    /// Add a clause of DIMACS literals. Returns false if the solver became trivially UNSAT.
    fn add_clause(&mut self, lits: &[i32]) -> bool;
    /// Solve. `Some(true)` = SAT, `Some(false)` = UNSAT, `None` = aborted/unknown.
    fn solve(&mut self) -> Option<bool>;
    /// Value of variable `v` (1-based) in the last model. Only valid after `solve()==Some(true)`.
    fn value_of(&self, v: u32) -> bool;
}

pub struct BatSat {
    s: Solver<batsat::BasicCallbacks>,
    vars: Vec<Var>,
    clauses: u64,
    buf: Vec<Lit>,
}

impl Default for BatSat {
    fn default() -> Self {
        BatSat { s: Solver::default(), vars: Vec::new(), clauses: 0, buf: Vec::new() }
    }
}

impl BatSat {
    pub fn new() -> Self {
        Self::default()
    }
    #[inline]
    fn lit(&self, l: i32) -> Lit {
        let v = self.vars[(l.unsigned_abs() - 1) as usize];
        Lit::new(v, l > 0)
    }
}

impl SatSolver for BatSat {
    fn num_vars(&self) -> u32 {
        self.vars.len() as u32
    }
    fn num_clauses(&self) -> u64 {
        self.clauses
    }
    fn add_variables(&mut self, n: u32) {
        for _ in 0..n {
            let v = self.s.new_var_default();
            self.vars.push(v);
        }
    }
    fn add_clause(&mut self, lits: &[i32]) -> bool {
        self.clauses += 1;
        let mut buf = std::mem::take(&mut self.buf);
        buf.clear();
        buf.extend(lits.iter().map(|&l| self.lit(l)));
        let ok = self.s.add_clause_reuse(&mut buf);
        self.buf = buf;
        ok
    }
    fn solve(&mut self) -> Option<bool> {
        let r = self.s.solve_limited(&[]);
        if r == lbool::TRUE {
            Some(true)
        } else if r == lbool::FALSE {
            Some(false)
        } else {
            None
        }
    }
    fn value_of(&self, v: u32) -> bool {
        self.s.value_var(self.vars[(v - 1) as usize]) == lbool::TRUE
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sat_and_unsat() {
        let mut s = BatSat::new();
        s.add_variables(2);
        assert!(s.add_clause(&[1, 2]));
        assert!(s.add_clause(&[-1]));
        assert_eq!(s.solve(), Some(true));
        assert!(!s.value_of(1));
        assert!(s.value_of(2));
        s.add_clause(&[-2]);
        assert_eq!(s.solve(), Some(false));
    }
}
