//! Port of edu.mit.csail.sdg.translator:
//!   TranslateAlloyToKodkod, ScopeComputer, BoundsComputer, A4Solution, A4Options, Simplifier.
//!
//! Public contract used by the CLI (extend, do not break):
//!   * [`execute_command`] ~ `TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), cmd, opt)`
//!   * [`Solution::next`]  ~ `A4Solution.next()`

use alloy_core::{AlloyError, World};
pub use kodkod; // relational engine used by the translator
use std::collections::BTreeMap;

/// Mirrors the subset of `A4Options` the harness uses. Defaults = Java defaults.
#[derive(Debug, Clone)]
pub struct Options {
    pub symmetry: i32,
    pub skolem_depth: i32,
    pub no_overflow: bool,
    pub unrolls: i32,
    pub want_instance: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options { symmetry: 20, skolem_depth: 0, no_overflow: false, unrolls: -1, want_instance: true }
    }
}

/// Same numbers Java reports through `A4Reporter.solve(plength, primaryVars, totalVars, clauses)`.
#[derive(Debug, Clone, Default)]
pub struct Stats {
    pub primary_vars: i64,
    pub vars: i64,
    pub clauses: i64,
}

/// Normalized instance: one map per state (static problems have exactly one state).
/// Keys: `this/Sig`, `this/Sig.field`, `skolem:$name`; tuples are atom names like `House$0`, sorted.
#[derive(Debug, Clone, Default)]
pub struct Instance {
    pub trace_length: i32,
    pub loop_state: i32,
    pub states: Vec<BTreeMap<String, Vec<Vec<String>>>>,
}

pub struct Solution {
    pub sat: bool,
    /// true iff the problem is temporal (Java: `A4Solution.getMinTrace() != -1`)
    pub temporal: bool,
    pub min_trace: i32,
    pub max_trace: i32,
    /// time to build bounds/translate to CNF (until the SAT call)
    pub translate_ms: f64,
    /// time spent in the SAT solver
    pub solve_ms: f64,
    pub stats: Stats,
    // TODO: hold the solver/translation state needed for instance() and next()
}

impl Solution {
    /// The current satisfying instance (None if UNSAT).
    pub fn instance(&self) -> Option<Instance> {
        None
    }
    /// Advance to the next solution (blocks the current one), like `A4Solution.next()`.
    /// Returns Ok(true) if a new solution was found.
    pub fn next(&mut self) -> Result<bool, AlloyError> {
        Err(AlloyError::unsupported("Solution::next not implemented yet"))
    }
}

/// Execute command number `index` of `world`.
pub fn execute_command(world: &World, index: usize, opt: &Options) -> Result<Solution, AlloyError> {
    let _ = (world, index, opt);
    Err(AlloyError::unsupported("translator not implemented yet (milestone M4)"))
}
