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

/// Java type-checks the whole root module when it loads. Runs the semantic pass and reports the *type errors* it
/// finds (other failures, e.g. not-yet-supported features, are not file-level errors).
pub fn check_types(world: &World) -> Result<(), AlloyError> {
    match sema::build(&world.modules) {
        Err(e) if e.kind == ErrorKind::Type => Err(e),
        _ => Ok(()),
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
    let temporal = model.temporal;
    let (min_trace, max_trace) = if temporal {
        let (smin, smax) = cmd.steps.map_or((None, -1), |(a, b)| (a, b));
        if smax == i32::MAX {
            // Java: the bounded engines cannot do unbounded (complete) model checking
            return Err(AlloyError::new(
                ErrorKind::Other,
                None,
                "Bounded engines do not support complete model checking.",
            ));
        }
        (smin.unwrap_or(1).max(1), if smax > 0 { smax } else { 10 })
    } else {
        (-1, -1)
    };
    let mut translate_ms = 0.0;
    let mut solve_ms = 0.0;
    let mut result = None;
    let mut trace_len = 1;
    let ks: Vec<Option<usize>> = if temporal { (min_trace..=max_trace).map(|k| Some(k as usize)).collect() } else { vec![None] };
    for k in ks {
        let t1 = Instant::now();
        let problem = translate::translate(&model, cmd, opt, k)?;
        translate_ms += t1.elapsed().as_secs_f64() * 1000.0;
        let t2 = Instant::now();
        let sol = kodkod::translate::solve(&problem.bounds, &problem.formula)
            .map_err(|e| AlloyError::new(ErrorKind::Other, None, e))?;
        solve_ms += t2.elapsed().as_secs_f64() * 1000.0;
        let sat = sol.sat == Some(true);
        trace_len = k.unwrap_or(1) as i32;
        result = Some((problem, sol));
        if sat {
            break;
        }
    }
    let (problem, sol) = result.ok_or_else(|| AlloyError::new(ErrorKind::Other, None, "no trace length to try"))?;
    let _ = t0;
    let instance = sol.instance.as_ref().map(|i| {
        if temporal {
            to_temporal_instance(&model, &problem.bounds, i, trace_len as usize)
        } else {
            to_instance(&model, &problem.bounds, i)
        }
    });
    Ok(Solution {
        sat: sol.sat == Some(true),
        temporal,
        min_trace,
        max_trace,
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

/// Splits the time column off the variable relations: one atom-name map per state, plus the loop position.
fn to_temporal_instance(model: &Model, bounds: &kodkod::instance::Bounds, inst: &kodkod::instance::Instance, k: usize) -> Instance {
    let mut var_names: std::collections::HashSet<String> = std::collections::HashSet::new();
    for s in &model.sigs {
        if s.is_var {
            var_names.insert(s.label.clone());
        }
    }
    for f in &model.fields {
        if f.is_var {
            var_names.insert(f.label.clone());
        }
    }
    let time_index = |a: u32| -> Option<usize> {
        bounds.universe.atom(a).strip_prefix("$time$").and_then(|x| x.parse::<usize>().ok())
    };
    let mut states: Vec<BTreeMap<String, Vec<Vec<String>>>> = vec![BTreeMap::new(); k];
    let mut loop_state = -1;
    for (name, ts) in &inst.relations {
        if name == "$loop" {
            if let Some(t) = ts.tuples.iter().next() {
                loop_state = time_index(t[0]).map_or(-1, |x| x as i32);
            }
            continue;
        }
        if name.starts_with('$') {
            continue;
        }
        if var_names.contains(name) {
            for st in states.iter_mut() {
                st.entry(name.clone()).or_default();
            }
            for t in &ts.tuples {
                let (last, rest) = t.split_last().unwrap();
                if let Some(si) = time_index(*last) {
                    states[si]
                        .entry(name.clone())
                        .or_default()
                        .push(rest.iter().map(|&a| bounds.universe.atom(a).to_string()).collect());
                }
            }
        } else {
            let tuples: Vec<Vec<String>> = ts
                .tuples
                .iter()
                .map(|t| t.iter().map(|&a| bounds.universe.atom(a).to_string()).collect())
                .collect();
            for st in states.iter_mut() {
                st.insert(name.clone(), tuples.clone());
            }
        }
    }
    Instance { trace_length: k as i32, loop_state, states }
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

#[cfg(test)]
mod temporal_tests {
    use super::*;

    fn run(src: &str, idx: usize) -> Result<Solution, AlloyError> {
        static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
        let n = N.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let dir = std::env::temp_dir().join(format!("alloy_rs_temporal_{}_{}", std::process::id(), n));
        std::fs::create_dir_all(&dir).unwrap();
        let f = dir.join("t.als");
        std::fs::write(&f, src).unwrap();
        let world = alloy_core::parse_everything_from_file(&f)?;
        execute_command(&world, idx, &Options::default())
    }

    #[test]
    fn eventually_needs_a_trace_and_always_can_stutter() {
        let src = [
            "var sig P {}",
            "run a { eventually some P } for 2",
            "check b { always (some P implies once some P) } for 2",
            "run c { always no P and eventually some P } for 2",
        ]
        .join("
");
        assert!(run(&src, 0).unwrap().sat);
        assert!(!run(&src, 1).unwrap().sat);
        assert!(!run(&src, 2).unwrap().sat);
    }

    #[test]
    fn past_operators_see_the_prefix_and_prime_wraps_to_the_loop() {
        let src = [
            "var sig P {}",
            "fact { some P and always (some P implies after no P) }",
            "run a { eventually (no P and once some P) } for 2",
            "run b { always some P } for 2",
        ]
        .join("
");
        assert!(run(&src, 0).unwrap().sat);
        assert!(!run(&src, 1).unwrap().sat);
    }

    #[test]
    fn unbounded_steps_are_an_error() {
        let src = "var sig P {}
run a { some P } for 2 but 1.. steps
";
        assert!(run(src, 0).is_err());
    }
}
