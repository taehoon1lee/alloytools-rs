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
    /// Abort `solve()` (returning `None`) after this many conflicts; `None` = unlimited.
    fn set_conflict_limit(&mut self, _limit: Option<u64>) {}
    /// Abort `solve()` (returning `None`) after this much wall-clock time; `None` = unlimited.
    fn set_time_limit(&mut self, _limit: Option<std::time::Duration>) {}
    /// Value of variable `v` (1-based) in the last model. Only valid after `solve()==Some(true)`.
    fn value_of(&self, v: u32) -> bool;
}

/// Stops the search after a number of learnt clauses (= conflicts).
#[derive(Default)]
pub struct Budget {
    pub limit: Option<u64>,
    pub learnt: u64,
    pub deadline: Option<std::time::Instant>,
}

impl batsat::Callbacks for Budget {
    fn on_new_clause(&mut self, _c: &[Lit], src: batsat::clause::Kind) {
        if src == batsat::clause::Kind::Learnt {
            self.learnt += 1;
        }
    }
    fn stop(&self) -> bool {
        self.limit.map_or(false, |l| self.learnt >= l) || self.deadline.map_or(false, |d| std::time::Instant::now() >= d)
    }
}

pub struct BatSat {
    time_limit: Option<std::time::Duration>,
    s: Solver<Budget>,
    vars: Vec<Var>,
    clauses: u64,
    buf: Vec<Lit>,
}

impl Default for BatSat {
    fn default() -> Self {
        let mut o = batsat::SolverOpts::default();
        // Geometric restarts like SAT4J's MiniSat restarts (the Java baseline); Luby restarts were up to 5x slower
        // on the hard UNSAT corpus models.
        o.luby_restart = false;
        let f = |k: &str| std::env::var(k).ok().and_then(|v| v.parse::<f64>().ok());
        if let Some(v) = f("KSAT_VD") {
            o.var_decay = v;
        }
        if let Some(v) = f("KSAT_LUBY") {
            o.luby_restart = v != 0.0;
        }
        if let Some(v) = f("KSAT_RF") {
            o.restart_first = v as i32;
        }
        if let Some(v) = f("KSAT_RI") {
            o.restart_inc = v;
        }
        if let Some(v) = f("KSAT_PS") {
            o.phase_saving = v as i32;
        }
        if let Some(v) = f("KSAT_CC") {
            o.ccmin_mode = v as i32;
        }
        if let Some(v) = f("KSAT_SEED") {
            o.random_seed = v;
        }
        if let Some(v) = f("KSAT_RND") {
            o.random_var_freq = v;
        }
        if let Some(v) = f("KSAT_LF") {
            o.learntsize_factor = v;
        }
        if let Some(v) = f("KSAT_LI") {
            o.learntsize_inc = v;
        }
        if let Some(v) = f("KSAT_CD") {
            o.clause_decay = v;
        }
        BatSat { time_limit: None, s: Solver::new(o, Budget::default()), vars: Vec::new(), clauses: 0, buf: Vec::new() }
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
    fn set_conflict_limit(&mut self, limit: Option<u64>) {
        self.s.cb_mut().limit = limit;
        self.s.cb_mut().learnt = 0;
    }
    fn set_time_limit(&mut self, limit: Option<std::time::Duration>) {
        // the clock starts when `solve()` is called, not while the formula is still being translated
        self.time_limit = limit;
    }
    fn num_vars(&self) -> u32 {
        self.vars.len() as u32
    }
    fn num_clauses(&self) -> u64 {
        self.clauses
    }
    fn add_variables(&mut self, n: u32) {
        for _ in 0..n {
            let v = match std::env::var("KSAT_POL").ok().as_deref() {
                Some("1") => self.s.new_var(lbool::TRUE, true),
                Some("0") => self.s.new_var(lbool::FALSE, true),
                _ => self.s.new_var_default(),
            };
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
        let t0 = std::time::Instant::now();
        self.s.cb_mut().deadline = self.time_limit.map(|d| t0 + d);
        let r = self.s.solve_limited(&[]);
        if std::env::var("KSAT_STATS").is_ok() {
            eprintln!("sat: conflicts {} time {:?} vars {} clauses {}", self.s.num_conflicts(), t0.elapsed(), self.vars.len(), self.clauses);
        }
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
