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

pub mod simp;

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
    /// Preprocess the CNF (variable elimination, [`simp`]) at the first `solve()`, keeping the `frozen` variables
    /// (1-based). Only for one-shot use: no clauses or assumptions over non-frozen variables may follow.
    /// `value_of` stays valid for every variable. Backends may ignore it.
    fn set_simplify(&mut self, _frozen: &[u32]) {}
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
    /// `Some(frozen)`: run [`simp::simplify`] before the first solve.
    simp_frozen: Option<Vec<u32>>,
    elim_stack: Vec<i32>,
    /// Model over all variables (1-based) after a satisfiable simplified solve.
    ext_model: Option<Vec<bool>>,
    opts: batsat::SolverOpts,
    /// conflicts before simplification (default [`SIMP_DELAY`])
    simp_delay: u64,
}

/// Conflicts spent on the unsimplified CNF before variable elimination is tried (easy problems never pay for it).
const SIMP_DELAY: u64 = 2_000;

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
        if std::env::var("KSAT_NOBIN").is_ok() {
            o.bin_watches = false;
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
            s: Solver::new(o.clone(), Budget::default()),
            vars: Vec::new(),
            clauses: 0,
            simp_frozen: None,
            elim_stack: Vec::new(),
            ext_model: None,
            opts: o,
            simp_delay: SIMP_DELAY,
        }
    }
}

impl BatSat {
    pub fn new() -> Self {
        Self::default()
    }

    /// Binary clauses in dedicated watch lists (default on; `KSAT_NOBIN` forces off). Call before adding clauses.
    /// It changes the propagation order and so the search path: portfolio configurations differ in it.
    pub fn set_binary_watches(&mut self, on: bool) {
        self.opts.bin_watches = on && std::env::var("KSAT_NOBIN").is_err();
        let cb = std::mem::take(self.s.cb_mut());
        self.s = Solver::new(self.opts.clone(), cb);
    }

    /// Conflicts spent before the simplification of [`SatSolver::set_simplify`] (tests, tuning).
    pub fn set_simplify_delay(&mut self, conflicts: u64) {
        self.simp_delay = conflicts;
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
    fn set_simplify(&mut self, frozen: &[u32]) {
        if std::env::var("KSAT_NOSIMP").is_err() {
            self.simp_frozen = Some(frozen.to_vec());
        }
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
            return self.run(None);
        }
        let pending = std::mem::take(&mut self.pending);
        let Some(frozen) = self.simp_frozen.take() else {
            if !self.build(&pending, &[]) {
                return Some(false);
            }
            return self.run(None);
        };
        // stage 1: the CNF as translated, for a few conflicts
        let deadline = self.time_limit.map(|d| std::time::Instant::now() + d);
        if !self.build(&pending, &[]) {
            return Some(false);
        }
        let user_limit = self.s.cb_mut().limit;
        let first = user_limit.map_or(self.simp_delay, |l| l.min(self.simp_delay));
        self.s.cb_mut().limit = Some(first);
        if let Some(r) = self.run(deadline) {
            return Some(r);
        }
        let used = self.s.cb_mut().learnt;
        let stopped = {
            let cb = self.s.cb_mut();
            cb.stop_flag.as_ref().map_or(false, |f| f.load(std::sync::atomic::Ordering::Relaxed))
                || cb.deadline.map_or(false, |d| std::time::Instant::now() >= d)
                || user_limit.map_or(false, |l| used >= l)
        };
        if stopped || used < first {
            return None;
        }
        // stage 2: variable elimination, then a fresh solver on the smaller CNF
        let mut mask = vec![false; self.n_vars as usize + 1];
        for &v in frozen.iter().chain(self.priority.iter()) {
            if v >= 1 && v <= self.n_vars {
                mask[v as usize] = true;
            }
        }
        let t0 = std::time::Instant::now();
        let r = simp::simplify(self.n_vars, &pending, &mask);
        drop(pending);
        if std::env::var("KSAT_STATS").is_ok() {
            let n_el = r.eliminated.iter().filter(|&&e| e).count();
            let n_cl = r.clauses.iter().filter(|&&l| l == 0).count();
            eprintln!("simp: {:?} eliminated {} vars, clauses {} -> {}", t0.elapsed(), n_el, self.clauses, n_cl);
        }
        if r.unsat {
            self.unsat = true;
            return Some(false);
        }
        let old = std::mem::take(self.s.cb_mut());
        let cb = Budget { limit: user_limit.map(|l| l - used), learnt: 0, deadline: None, stop_flag: old.stop_flag };
        self.s = Solver::new(self.opts.clone(), cb);
        self.elim_stack = r.elim_stack;
        if !self.build(&r.clauses, &r.eliminated) {
            return Some(false);
        }
        self.run(deadline)
    }
    fn solve_assuming(&mut self, assumptions: &[i32]) -> Option<bool> {
        if self.unsat {
            return Some(false);
        }
        // assumptions may mention any variable: no elimination
        self.simp_frozen = None;
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
        if let Some(m) = &self.ext_model {
            return m[v as usize];
        }
        self.s.value_var(self.solved_vars[(v - 1) as usize]) == lbool::TRUE
    }
}

impl BatSat {
    /// Creates the solver variables (priority ones first, then the rest in id order; `eliminated` ones are not
    /// decision variables) and loads `clauses` (flat, 0-terminated). Returns false if trivially unsatisfiable.
    fn build(&mut self, clauses: &[i32], eliminated: &[bool]) -> bool {
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
            // eliminated variables occur in no clause: never branch on them
            let dvar = !eliminated.get(v as usize).copied().unwrap_or(false);
            let sv = match self.init_pol {
                Some(true) => self.s.new_var(lbool::TRUE, dvar),
                Some(false) => self.s.new_var(lbool::FALSE, dvar),
                None => self.s.new_var(lbool::UNDEF, dvar),
            };
            var_of[v as usize] = Some(sv);
        }
        self.vars = (1..=self.n_vars).map(|v| var_of[v as usize].unwrap()).collect();
        self.solved_vars = self.vars.clone();
        self.built = true;
        // Debug knob: KSAT_DUMP=<file> writes the CNF (DIMACS, solver numbering) before the first solve.
        if let Ok(path) = std::env::var("KSAT_DUMP") {
            if eliminated.is_empty() {
                use std::io::Write;
                let n_cl = clauses.iter().filter(|&&l| l == 0).count();
                let mut out = String::with_capacity(clauses.len() * 7);
                out.push_str(&format!("p cnf {} {}\n", self.n_vars, n_cl));
                for &l in clauses {
                    let v = if l == 0 { 0 } else { (self.vars[(l.unsigned_abs() - 1) as usize].idx() as i32 + 1) * l.signum() };
                    out.push_str(&v.to_string());
                    out.push(if l == 0 { '\n' } else { ' ' });
                }
                if let Ok(mut f) = std::fs::File::create(&path) {
                    let _ = f.write_all(out.as_bytes());
                }
            }
        }
        let mut buf: Vec<Lit> = Vec::new();
        for chunk in clauses.split(|&l| l == 0) {
            if chunk.is_empty() {
                continue;
            }
            buf.clear();
            buf.extend(chunk.iter().map(|&l| Lit::new(self.vars[(l.unsigned_abs() - 1) as usize], l > 0)));
            if !self.s.add_clause_reuse(&mut buf) {
                self.unsat = true;
                return false;
            }
        }
        true
    }

    /// Search statistics of the last solve (diagnostics).
    pub fn stats_line(&self) -> String {
        format!(
            "conflicts {} decisions {} propagations {} restarts {}",
            self.s.num_conflicts(),
            self.s.num_decisions(),
            self.s.num_propagations(),
            self.s.num_restarts()
        )
    }

    /// Solves; `deadline` overrides the one derived from `set_time_limit` (measured from now).
    fn run(&mut self, deadline: Option<std::time::Instant>) -> Option<bool> {
        let t0 = std::time::Instant::now();
        self.s.cb_mut().deadline = deadline.or_else(|| self.time_limit.map(|d| t0 + d));
        let r = self.s.solve_limited(&[]);
        if std::env::var("KSAT_STATS").is_ok() {
            eprintln!("sat: conflicts {} time {:?} vars {} clauses {}", self.s.num_conflicts(), t0.elapsed(), self.n_vars, self.clauses);
        }
        if r == lbool::TRUE {
            if !self.elim_stack.is_empty() {
                let mut m = vec![false; self.n_vars as usize + 1];
                for v in 1..=self.n_vars {
                    m[v as usize] = self.s.value_var(self.vars[(v - 1) as usize]) == lbool::TRUE;
                }
                simp::extend_model(&self.elim_stack, &mut m);
                self.ext_model = Some(m);
            }
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

    /// Random 2/3-CNFs around the phase transition, solved with and without the elimination stage, against brute force.
    #[test]
    fn random_cnfs_match_brute_force() {
        let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut rnd = |m: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % m
        };
        for round in 0..300 {
            let n = 6 + rnd(7) as u32;
            let m = (n as f64 * (3.0 + rnd(30) as f64 / 20.0)) as usize;
            let cls: Vec<Vec<i32>> = (0..m)
                .map(|_| {
                    let len = 2 + rnd(2);
                    (0..len).map(|_| (1 + rnd(n as u64) as i32) * if rnd(2) == 0 { 1 } else { -1 }).collect()
                })
                .collect();
            let holds = |val: &dyn Fn(u32) -> bool| cls.iter().all(|c| c.iter().any(|&l| val(l.unsigned_abs()) == (l > 0)));
            let expected = (0..(1u32 << n)).any(|bits| holds(&|v| bits & (1 << (v - 1)) != 0));
            for simp in [false, true] {
                let mut s = BatSat::configured(round % 2 == 0, 0.0, 0, Some(round % 3 == 0));
                s.add_variables(n);
                for c in &cls {
                    s.add_clause(c);
                }
                if simp {
                    s.set_simplify(&[1, 2]);
                    s.set_simplify_delay(0);
                }
                let r = s.solve();
                assert_eq!(r, Some(expected), "round {round} simp {simp}: {cls:?}");
                if expected {
                    assert!(holds(&|v| s.value_of(v)), "round {round} simp {simp}: model violates {cls:?}");
                }
            }
        }
    }
}
