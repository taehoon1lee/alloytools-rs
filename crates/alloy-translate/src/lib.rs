//! Port of edu.mit.csail.sdg.translator:
//!   ScopeComputer (scopes + atom creation), BoundsComputer (sig/field bounds),
//!   TranslateAlloyToKodkod (facts, sig/field constraints, run/check formulas), A4Solution (instance).
//!
//! Public contract used by the CLI (extend, do not break):
//!   * [`execute_command`] ~ `TranslateAlloyToKodkod.execute_command(rep, world, cmd, opt)`
//!   * [`Solution::instance`] ~ `A4Solution.getOriginalInstance` (informational)
//!
//! Not yet: integers (bitwidth > 0 atoms and arithmetic), strings, sequences, temporal logic,
//! symmetry breaking, skolemization, `pred/totalOrder` and `disj` translation, solution enumeration.
//! Anything not handled returns `AlloyError::unsupported`, never a guessed answer.

mod scope;
mod translate;

use std::collections::BTreeMap;
use std::time::Instant;

use alloy_core::error::{AlloyError, ErrorKind};
use alloy_core::sema::{self, Model, RCommand};
use alloy_core::World;
pub use kodkod;

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
        Options {
            symmetry: 20,
            skolem_depth: 0,
            no_overflow: false,
            unrolls: -1,
            want_instance: true,
        }
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
/// Keys: `this/Sig`, `this/Sig.field`; tuples are atom names like `House$0`, sorted.
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
    instance: Option<Instance>,
}

impl Solution {
    /// The current satisfying instance (None if UNSAT).
    pub fn instance(&self) -> Option<Instance> {
        self.instance.clone()
    }
    /// Advance to the next solution (blocks the current one), like `A4Solution.next()`.
    /// Returns Ok(true) if a new solution was found.
    pub fn next(&mut self) -> Result<bool, AlloyError> {
        Err(AlloyError::unsupported("Solution::next not implemented yet (M7)"))
    }
}

/// Execute command number `index` of `world` (the root module's `index`-th command).
pub fn execute_command(world: &World, index: usize, opt: &Options) -> Result<Solution, AlloyError> {
    let t0 = Instant::now();
    let model = sema::build(&world.modules)?;
    let cmd: &RCommand = model
        .commands
        .get(index)
        .ok_or_else(|| AlloyError::new(ErrorKind::Other, None, format!("no command {index}")))?;
    let problem = translate::translate(&model, cmd, opt)?;
    let translate_ms = t0.elapsed().as_secs_f64() * 1000.0;

    let t1 = Instant::now();
    let sol = kodkod::translate::solve(&problem.bounds, &problem.formula)
        .map_err(|e| AlloyError::new(ErrorKind::Other, None, e))?;
    let solve_ms = t1.elapsed().as_secs_f64() * 1000.0;

    let instance = sol
        .instance
        .as_ref()
        .map(|i| to_instance(&model, &problem.bounds, i));
    Ok(Solution {
        sat: sol.sat == Some(true),
        temporal: false,
        min_trace: -1,
        max_trace: -1,
        translate_ms,
        solve_ms,
        stats: Stats {
            primary_vars: sol.primary_vars as i64,
            vars: sol.vars as i64,
            clauses: sol.clauses as i64,
        },
        instance,
    })
}

/// Atom names of every relation of a kodkod instance, under the Java key names.
fn to_instance(_model: &Model, bounds: &kodkod::instance::Bounds, inst: &kodkod::instance::Instance) -> Instance {
    let mut st = BTreeMap::new();
    for (name, ts) in &inst.relations {
        if name.starts_with('$') {
            continue;
        }
        let tuples: Vec<Vec<String>> = ts
            .tuples
            .iter()
            .map(|t| t.iter().map(|&a| bounds.universe.atom(a).to_string()).collect())
            .collect();
        st.insert(name.clone(), tuples);
    }
    Instance {
        trace_length: 1,
        loop_state: -1,
        states: vec![st],
    }
}

/// Re-exported for the scope tests and the CLI's diagnostics.
pub use scope::compute_scopes;
