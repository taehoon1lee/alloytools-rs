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
    /// Variables (1-based DIMACS ids) the solver should branch on first (Kodkod numbers primary variables first).
    fn set_priority(&mut self, _vars: &[u32]) {}
    /// Solves under assumptions (literals as in `add_clause`); `None` when unsupported or interrupted.
    fn solve_assuming(&mut self, _assumptions: &[i32]) -> Option<bool> {
        None
    }
    /// Abort `solve()` (returning `None`) after this many conflicts; `None` = unlimited.
    fn set_conflict_limit(&mut self, _limit: Option<u64>) {}
    /// Abort `solve()` (returning `None`) once the flag is set (portfolio races).
    fn set_stop_flag(&mut self, _flag: std::sync::Arc<std::sync::atomic::AtomicBool>) {}
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
    /// Set by another thread of a portfolio race when it already has the answer.
    pub stop_flag: Option<std::sync::Arc<std::sync::atomic::AtomicBool>>,
}

impl batsat::Callbacks for Budget {
    fn on_new_clause(&mut self, _c: &[Lit], src: batsat::clause::Kind) {
        if src == batsat::clause::Kind::Learnt {
            self.learnt += 1;
        }
    }
    fn stop(&self) -> bool {
        self.limit.map_or(false, |l| self.learnt >= l)
            || self.deadline.map_or(false, |d| std::time::Instant::now() >= d)
            || self.stop_flag.as_ref().map_or(false, |f| f.load(std::sync::atomic::Ordering::Relaxed))
    }
}

pub struct BatSat {
    /// Clauses are buffered (flat, 0-terminated) and the solver variables are created at `solve()` in priority
    /// order, so decisions start on the primary / skolem variables like Kodkod's variable numbering.
    pending: Vec<i32>,
    n_vars: u32,
    priority: Vec<u32>,
    unsat: bool,
    solved_vars: Vec<Var>,
    init_pol: Option<bool>,
    built: bool,
    time_limit: Option<std::time::Duration>,
    s: Solver<Budget>,
    vars: Vec<Var>,
    clauses: u64,
}

impl Default for BatSat {
    fn default() -> Self {
        Self::with_luby(false)
    }
}

impl BatSat {
    /// `luby = true`: Luby restarts (an alternative search schedule for portfolio runs); the default is geometric.
    pub fn with_luby(luby: bool) -> Self {
        Self::configured(luby, 0.0, 0, None)
    }

    /// Portfolio configuration: restart schedule, random-decision frequency, random seed (0 = default) and the
    /// initial branching polarity (`None` = solver default, i.e. false first).
    pub fn configured(luby: bool, random_var_freq: f64, seed: u32, init_pol: Option<bool>) -> Self {
        let mut o = batsat::SolverOpts::default();
        o.random_var_freq = random_var_freq;
        if seed != 0 {
            o.random_seed = seed as f64;
        }
        // Geometric restarts like SAT4J's MiniSat restarts (the Java baseline); Luby restarts were up to 5x slower
        // on the hard UNSAT corpus models.
        o.luby_restart = luby;
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
        BatSat {
            pending: Vec::new(),
            n_vars: 0,
            priority: Vec::new(),
            unsat: false,
            solved_vars: Vec::new(),
            init_pol,
            built: false,
            time_limit: None,
            s: Solver::new(o, Budget::default()),
            vars: Vec::new(),
            clauses: 0,
        }
    }
}

impl BatSat {
    pub fn new() -> Self {
        Self::default()
    }
}

impl SatSolver for BatSat {
    fn set_stop_flag(&mut self, flag: std::sync::Arc<std::sync::atomic::AtomicBool>) {
        self.s.cb_mut().stop_flag = Some(flag);
    }
    fn set_conflict_limit(&mut self, limit: Option<u64>) {
        self.s.cb_mut().limit = limit;
        self.s.cb_mut().learnt = 0;
    }
    fn set_time_limit(&mut self, limit: Option<std::time::Duration>) {
        // the clock starts when `solve()` is called, not while the formula is still being translated
        self.time_limit = limit;
    }
    fn num_vars(&self) -> u32 {
        self.n_vars
    }
    fn num_clauses(&self) -> u64 {
        self.clauses
    }
    fn add_variables(&mut self, n: u32) {
        self.n_vars += n;
        if self.built {
            for _ in 0..n {
                let v = self.s.new_var_default();
                self.solved_vars.push(v);
            }
        }
    }
    fn set_priority(&mut self, vars: &[u32]) {
        self.priority = vars.to_vec();
    }
    fn add_clause(&mut self, lits: &[i32]) -> bool {
        self.clauses += 1;
        if lits.is_empty() {
            self.unsat = true;
            return false;
        }
        if self.built {
            // incremental use after the first solve: the variables already exist
            let mut buf: Vec<Lit> =
                lits.iter().map(|&l| Lit::new(self.solved_vars[(l.unsigned_abs() - 1) as usize], l > 0)).collect();
            let ok = self.s.add_clause_reuse(&mut buf);
            if !ok {
                self.unsat = true;
            }
            return ok;
        }
        self.pending.extend_from_slice(lits);
        self.pending.push(0);
        true
    }
    fn solve(&mut self) -> Option<bool> {
        if self.unsat {
            return Some(false);
        }
        if self.built {
            return self.run();
        }
        // create the solver variables: priority ones first, then the rest in id order
        let mut order: Vec<u32> = Vec::with_capacity(self.n_vars as usize);
        let mut seen = vec![false; self.n_vars as usize + 1];
        for &v in &self.priority {
            if v >= 1 && v <= self.n_vars && !seen[v as usize] {
                seen[v as usize] = true;
                order.push(v);
            }
        }
        for v in 1..=self.n_vars {
            if !seen[v as usize] {
                order.push(v);
            }
        }
        let mut var_of = vec![None; self.n_vars as usize + 1];
        for v in order {
            let sv = match self.init_pol {
                Some(true) => self.s.new_var(lbool::TRUE, true),
                Some(false) => self.s.new_var(lbool::FALSE, true),
                None => self.s.new_var_default(),
            };
            var_of[v as usize] = Some(sv);
        }
        self.vars = (1..=self.n_vars).map(|v| var_of[v as usize].unwrap()).collect();
        let pending = std::mem::take(&mut self.pending);
        let mut buf: Vec<Lit> = Vec::new();
        for chunk in pending.split(|&l| l == 0) {
            if chunk.is_empty() {
                continue;
            }
            buf.clear();
            buf.extend(chunk.iter().map(|&l| Lit::new(self.vars[(l.unsigned_abs() - 1) as usize], l > 0)));
            if !self.s.add_clause_reuse(&mut buf) {
                return Some(false);
            }
        }
        self.solved_vars = self.vars.clone();
        self.built = true;
        self.run()
    }
    fn solve_assuming(&mut self, assumptions: &[i32]) -> Option<bool> {
        if self.unsat {
            return Some(false);
        }
        if !self.built && self.solve().is_none() {
            return None;
        }
        if self.unsat {
            return Some(false);
        }
        let lits: Vec<Lit> =
            assumptions.iter().map(|&l| Lit::new(self.vars[(l.unsigned_abs() - 1) as usize], l > 0)).collect();
        let r = self.s.solve_limited(&lits);
        if r == lbool::TRUE {
            self.solved_vars = self.vars.clone();
            Some(true)
        } else if r == lbool::FALSE {
            Some(false)
        } else {
            None
        }
    }
    fn value_of(&self, v: u32) -> bool {
        self.s.value_var(self.solved_vars[(v - 1) as usize]) == lbool::TRUE
    }
}

impl BatSat {
    fn run(&mut self) -> Option<bool> {
        let t0 = std::time::Instant::now();
        self.s.cb_mut().deadline = self.time_limit.map(|d| t0 + d);
        let r = self.s.solve_limited(&[]);
        if std::env::var("KSAT_STATS").is_ok() {
            eprintln!("sat: conflicts {} time {:?} vars {} clauses {}", self.s.num_conflicts(), t0.elapsed(), self.n_vars, self.clauses);
        }
        if r == lbool::TRUE {
            Some(true)
        } else if r == lbool::FALSE {
            Some(false)
        } else {
            None
        }
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
