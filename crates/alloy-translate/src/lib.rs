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

pub mod exact;
mod resolve;
mod scope;
mod translate;

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
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
        Err(AlloyError::unsupported(
            "Solution::next not implemented yet (M7)",
        ))
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

type ExactJob = (std::thread::JoinHandle<Result<exact::ExactOutcome, AlloyError>>, Arc<AtomicBool>);

/// Starts the exact pipeline (Java-identical translation + SAT4J, `exact::solve_first`) on its own thread: it
/// yields the very instance Java reports. The fast pipeline decides the verdict; the exact one is only waited for
/// when the command is SAT (and stopped otherwise).
fn spawn_exact(world: &World, model: &Model, index: usize, opt: &Options) -> Option<ExactJob> {
    if !opt.want_instance || std::env::var("ALLOY_RS_NO_EXACT").is_ok() {
        return None;
    }
    let (w, m, sym) = (world.clone(), model.clone(), opt.symmetry);
    let stop = Arc::new(AtomicBool::new(false));
    let s2 = stop.clone();
    let h = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || exact::solve_first(&w, &m, index, sym, Some(s2)))
        .ok()?;
    Some((h, stop))
}

/// Execute command number `index` of `world` (the root module's `index`-th command).
pub fn execute_command(world: &World, index: usize, opt: &Options) -> Result<Solution, AlloyError> {
    let model = sema::build(&world.modules)?;
    let job = spawn_exact(world, &model, index, opt);
    let r = execute_fast(world, &model, index, opt);
    let Some((h, stop)) = job else { return r };
    match r {
        Ok(mut sol) if sol.sat => {
            if let Ok(Ok(out)) = h.join() {
                if out.sat {
                    if let Some(states) = out.instance {
                        sol.instance = Some(Instance { trace_length: states.len() as i32, loop_state: out.loop_state, states });
                    }
                }
            }
            Ok(sol)
        }
        other => {
            // UNSAT or error: the exact run is not needed (its thread ends at the next SAT4J stop check)
            stop.store(true, Ordering::Relaxed);
            other
        }
    }
}

/// The verdict (and a fallback instance) from the optimized pipeline.
fn execute_fast(world: &World, model: &Model, index: usize, opt: &Options) -> Result<Solution, AlloyError> {
    let _ = world;
    let t0 = Instant::now();
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
    let ks: Vec<Option<usize>> = if temporal {
        (min_trace..=max_trace).map(|k| Some(k as usize)).collect()
    } else {
        vec![None]
    };
    let mut run = |k: Option<usize>| -> Result<(translate::Problem, kodkod::translate::Solution), AlloyError> {
        let t1 = Instant::now();
        let problem = translate::translate(&model, cmd, opt, k)?;
        translate_ms += t1.elapsed().as_secs_f64() * 1000.0;
        let t2 = Instant::now();
        let sol = kodkod::translate::solve(&problem.bounds, &problem.formula)
            .map_err(|e| AlloyError::new(ErrorKind::Other, None, e))?;
        solve_ms += t2.elapsed().as_secs_f64() * 1000.0;
        Ok((problem, sol))
    };
    // Java (Pardinus) tries the trace lengths min..max in order and stops at the first SAT one. Traces are infinite
    // lassos, and a lasso of k states unrolls into one of k+1 states, so SAT(k) implies SAT(k+1): once two lengths
    // were UNSAT, the longest length is tried; if it is UNSAT, so is every shorter one (same answer, fewer solves).
    // If it is SAT, the search continues upwards as in Java, so the reported trace is still the shortest one.
    let mut probe: Option<(translate::Problem, kodkod::translate::Solution)> = None;
    let mut probed = !temporal || ks.len() <= 3 || std::env::var("KTRACE_ALL").is_ok();
    for (n, &k) in ks.iter().enumerate() {
        if !probed && n == 2 {
            probed = true;
            let (problem, sol) = run(ks[ks.len() - 1])?;
            if sol.sat == Some(false) {
                trace_len = max_trace;
                result = Some((problem, sol));
                break;
            }
            if sol.sat == Some(true) {
                probe = Some((problem, sol));
            }
        }
        let (problem, sol) = if n + 1 == ks.len() && probe.is_some() {
            probe.take().unwrap()
        } else {
            run(k)?
        };
        let sat = sol.sat == Some(true);
        trace_len = k.unwrap_or(1) as i32;
        result = Some((problem, sol));
        if sat {
            break;
        }
    }
    let (problem, sol) =
        result.ok_or_else(|| AlloyError::new(ErrorKind::Other, None, "no trace length to try"))?;
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
fn to_temporal_instance(
    model: &Model,
    bounds: &kodkod::instance::Bounds,
    inst: &kodkod::instance::Instance,
    k: usize,
) -> Instance {
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
        bounds
            .universe
            .atom(a)
            .strip_prefix("$time$")
            .and_then(|x| x.parse::<usize>().ok())
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
                    states[si].entry(name.clone()).or_default().push(
                        rest.iter()
                            .map(|&a| bounds.universe.atom(a).to_string())
                            .collect(),
                    );
                }
            }
        } else {
            let tuples: Vec<Vec<String>> = ts
                .tuples
                .iter()
                .map(|t| {
                    t.iter()
                        .map(|&a| bounds.universe.atom(a).to_string())
                        .collect()
                })
                .collect();
            for st in states.iter_mut() {
                st.insert(name.clone(), tuples.clone());
            }
        }
    }
    Instance {
        trace_length: k as i32,
        loop_state,
        states,
    }
}

/// Number of solutions of command `index` (Kodkod `solveAll` semantics, no symmetry breaking), counted up to `limit`:
/// `(count, capped)`. Temporal problems are counted at the first trace length that has a solution.
pub fn count_solutions(
    world: &World,
    index: usize,
    opt: &Options,
    limit: u32,
) -> Result<(u32, bool), AlloyError> {
    let model = sema::build(&world.modules)?;
    let cmd: &RCommand = model
        .commands
        .get(index)
        .ok_or_else(|| AlloyError::new(ErrorKind::Other, None, format!("no command {index}")))?;
    let kerr = |e: String| AlloyError::new(ErrorKind::Other, None, e);
    if !model.temporal {
        let problem = translate::translate(&model, cmd, opt, None)?;
        return kodkod::translate::count_all(&problem.bounds, &problem.formula, limit)
            .map_err(kerr);
    }
    // Temporal (Pardinus `next()`): after the first solution the static part is fixed and only different traces are
    // enumerated, over increasing trace lengths; a trace is counted once, at its minimal lasso length.
    let (smin, smax) = cmd.steps.map_or((None, -1), |(a, b)| (a, b));
    if smax == i32::MAX {
        return Err(AlloyError::new(
            ErrorKind::Other,
            None,
            "Bounded engines do not support complete model checking.",
        ));
    }
    let (min_k, max_k) = (smin.unwrap_or(1).max(1), if smax > 0 { smax } else { 10 });
    // Each entry is `(ordinal among non-$ relations, display name, tuples)` so multiple relations with the
    // same label (e.g. two opened module instances) are pinned independently across trace lengths `k`.
    let mut statics: Option<Vec<(usize, String, kodkod::instance::TupleSet)>> = None;
    let mut total = 0u32;
    for k in min_k..=max_k {
        let mut problem = translate::translate(&model, cmd, opt, Some(k as usize))?;
        let info = problem
            .trace
            .clone()
            .ok_or_else(|| AlloyError::new(ErrorKind::Other, None, "no trace info"))?;
        let non_internal: Vec<usize> = problem
            .bounds
            .relations
            .iter()
            .enumerate()
            .filter(|(_, rb)| !rb.name.starts_with('$'))
            .map(|(i, _)| i)
            .collect();
        if statics.is_none() {
            let static_ids: Vec<usize> = non_internal
                .iter()
                .copied()
                .filter(|&i| {
                    let rb = &problem.bounds.relations[i];
                    !info.var_rels.contains(&(i as u32)) && rb.upper.tuples != rb.lower.tuples
                })
                .collect();
            let Some(inst) =
                kodkod::translate::first_instance(&problem.bounds, &problem.formula, &static_ids)
                    .map_err(kerr)?
            else {
                continue;
            };
            let mut st = Vec::new();
            for (ord, &id) in non_internal.iter().enumerate() {
                let rb = &problem.bounds.relations[id];
                if info.var_rels.contains(&(id as u32)) || rb.upper.tuples == rb.lower.tuples {
                    continue;
                }
                if let Some(ts) = inst.by_id.get(id) {
                    st.push((ord, rb.name.clone(), ts.clone()));
                }
            }
            if std::env::var("KCOUNT").is_ok() {
                for (ord, n, ts) in &st {
                    eprintln!("static #{ord} {n}: {:?}", ts.tuples);
                }
            }
            statics = Some(st);
        }
        let mut extra: Vec<kodkod::ast::Formula> = vec![problem.formula.clone()];
        for (ord, name, ts) in statics.as_ref().unwrap() {
            let Some(&id) = non_internal.get(*ord) else {
                continue;
            };
            debug_assert_eq!(problem.bounds.relations[id].name, *name);
            extra.push(kodkod::ast::Formula::Equal(
                kodkod::ast::Expr::Rel(id as u32),
                kodkod::ast::Expr::Literal(ts.clone()),
            ));
        }
        extra.push(canonical_lasso(&info));
        problem.formula = kodkod::ast::Formula::And(extra);
        let mut proj: Vec<usize> = info.var_rels.iter().map(|r| *r as usize).collect();
        proj.push(info.loop_rel as usize);
        let (c, capped) = kodkod::translate::count_projected(
            &problem.bounds,
            &problem.formula,
            limit - total,
            Some(&proj),
        )
        .map_err(kerr)?;
        if std::env::var("KCOUNT").is_ok() {
            eprintln!(
                "k={k} count={c} capped={capped} var_rels={:?}",
                info.var_rels
            );
        }
        total += c;
        if capped {
            return Ok((total, true));
        }
        if total >= limit {
            // exactly `limit` found so far: more may exist at longer traces; probe by asking for one more later
            continue;
        }
    }
    Ok((total, false))
}

/// The loop is the minimal representation of its infinite trace: no earlier state equals the last one (the
/// prefix cannot shrink) and the loop part is not a repetition of a shorter period.
fn canonical_lasso(info: &translate::TraceInfo) -> kodkod::ast::Formula {
    use kodkod::ast::{Expr, Formula};
    let k = info.k;
    let eq_state = |i: usize, j: usize| -> Formula {
        let mut parts = Vec::new();
        for &r in &info.var_rels {
            parts.push(Formula::Equal(
                Expr::join(Expr::Rel(r), Expr::Rel(info.time_rel[i])),
                Expr::join(Expr::Rel(r), Expr::Rel(info.time_rel[j])),
            ));
        }
        Formula::And(parts)
    };
    let mut cases = Vec::new();
    for l in 0..k {
        let is_l = Formula::Subset(Expr::Rel(info.time_rel[l]), Expr::Rel(info.loop_rel));
        let mut conds = Vec::new();
        if l > 0 {
            conds.push(Formula::Not(Box::new(eq_state(l - 1, k - 1))));
        }
        let q = k - l;
        for q2 in 1..q {
            if q % q2 == 0 {
                let rep: Vec<Formula> = (l..k - q2).map(|j| eq_state(j, j + q2)).collect();
                conds.push(Formula::Not(Box::new(Formula::And(rep))));
            }
        }
        cases.push(Formula::Implies(
            Box::new(is_l),
            Box::new(Formula::And(conds)),
        ));
    }
    Formula::And(cases)
}

/// Atom names of every relation of a kodkod instance, under the Java key names.
fn to_instance(
    _model: &Model,
    bounds: &kodkod::instance::Bounds,
    inst: &kodkod::instance::Instance,
) -> Instance {
    let mut st = BTreeMap::new();
    for (name, ts) in &inst.relations {
        if name.starts_with('$') {
            continue;
        }
        let tuples: Vec<Vec<String>> = ts
            .tuples
            .iter()
            .map(|t| {
                t.iter()
                    .map(|&a| bounds.universe.atom(a).to_string())
                    .collect()
            })
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
        let dir =
            std::env::temp_dir().join(format!("alloy_rs_temporal_{}_{}", std::process::id(), n));
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
        .join(
            "
",
        );
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
        .join(
            "
",
        );
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

    fn count_src(files: &[(&str, &str)], main_file: &str, idx: usize, limit: u32) -> Result<(u32, bool), AlloyError> {
        static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(1000);
        let n = N.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let dir =
            std::env::temp_dir().join(format!("alloy_rs_count_{}_{}", std::process::id(), n));
        std::fs::create_dir_all(&dir).unwrap();
        for (name, content) in files {
            std::fs::write(dir.join(name), content).unwrap();
        }
        let world = alloy_core::parse_everything_from_file(&dir.join(main_file))?;
        let mut opt = Options::default();
        opt.symmetry = 0;
        opt.want_instance = false;
        count_solutions(&world, idx, &opt, limit)
    }

    #[test]
    fn enum_ordering_is_prebound_in_count() {
        // 3-element enum has a single fixed declaration order (A -> B -> C), not 3! = 6 permutations.
        let src = "\
enum E { A, B, C }
sig X { e: one E }
run {} for exactly 1 X
run { A.next = B and B.next = C and no C.next } for exactly 1 X
run { B.next = A } for exactly 1 X
";
        assert_eq!(count_src(&[("m.als", src)], "m.als", 0, 100).unwrap(), (3, false));
        assert_eq!(count_src(&[("m.als", src)], "m.als", 1, 100).unwrap(), (3, false));
        assert_eq!(count_src(&[("m.als", src)], "m.als", 2, 100).unwrap(), (0, false));
    }

    #[test]
    fn temporal_count_handles_enum_and_duplicate_static_relation_names() {
        // Two module instances declare static fields with the same label (`this/Box.v`) in a temporal model.
        let helper = "\
module helper[T]
one sig Box { v: one T }
";
        let main = "\
open helper[A] as h1
open helper[B] as h2
enum Color { Red, Green }
sig A {}
sig B {}
var sig P in A {}
run {} for exactly 2 A, exactly 2 B, 2 steps
";
        let (c, capped) = count_src(&[("helper.als", helper), ("main.als", main)], "main.als", 0, 100).unwrap();
        assert!(c > 0 && !capped, "expected positive finite trace count, got ({c}, {capped})");
    }
}
