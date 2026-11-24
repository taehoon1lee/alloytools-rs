//! Port of edu.mit.csail.sdg.translator:
//!   ScopeComputer (scopes + atom creation), BoundsComputer (sig/field bounds),
//!   TranslateAlloyToKodkod (facts, sig/field constraints, run/check formulas), A4Solution (instance).
//!
//! Public contract used by the CLI (extend, do not break):
//!   * [`execute_command`] ~ `TranslateAlloyToKodkod.execute_command(rep, world, cmd, opt)`
//!   * [`Solution::instance`] ~ `A4Solution.getOriginalInstance` (informational)
//!
//! Single pure-MIT pipeline: Alloy -> Pardinus AST (`exact`) -> `pardinus` Boolean circuit / CNF -> `batsat`.

pub mod eval;
pub mod exact;
pub mod xml;
pub use eval::{
    eval_expr, verify_instance, AtomIdx, EvalError, RelVal, StateValuation, TraceEnv, Universe,
    Value, VerificationError, VerificationKind,
};
pub use xml::{
    encode_xml, write_metamodel_xml, write_solution_xml, XmlData, XmlField, XmlSig, XmlSkolem,
    XmlState,
};
mod resolve;
mod scope;

use std::collections::BTreeMap;

use alloy_core::error::{AlloyError, ErrorKind};
use alloy_core::sema;
use alloy_core::World;
pub use pardinus;

/// Mirrors the subset of `A4Options` the harness uses. Defaults = Java defaults.
#[derive(Debug, Clone)]
pub struct Options {
    pub symmetry: i32,
    pub skolem_depth: i32,
    pub no_overflow: bool,
    pub unrolls: i32,
    pub want_instance: bool,
    pub want_xml: bool,
    pub verify: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            symmetry: 20,
            skolem_depth: 0,
            no_overflow: false,
            unrolls: -1,
            want_instance: true,
            want_xml: false,
            verify: false,
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
    xml_data: Option<XmlData>,
}

impl Solution {
    /// The current satisfying instance (None if UNSAT).
    pub fn instance(&self) -> Option<Instance> {
        self.instance.clone()
    }
    /// Raw structured XML metadata + states (only populated when `Options::want_xml` is set).
    pub fn xml_data(&self) -> Option<&XmlData> {
        self.xml_data.as_ref()
    }
    /// Formats the satisfying instance as Java Alloy 6.2.0 compatible XML (None if UNSAT or `want_xml` was false).
    pub fn to_xml(&self) -> Option<String> {
        self.xml_data.as_ref().map(xml::write_solution_xml)
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

/// Execute command number `index` of `world` (the root module's `index`-th command).
pub fn execute_command(world: &World, index: usize, opt: &Options) -> Result<Solution, AlloyError> {
    let model = sema::build(&world.modules)?;
    let do_verify = opt.verify
        || std::env::var("ALLOY_RS_VERIFY").map_or(false, |v| !v.is_empty() && v != "0");
    let mut solve_opt;
    let effective_opt = if (do_verify || opt.want_xml) && !opt.want_instance {
        solve_opt = opt.clone();
        solve_opt.want_instance = true;
        &solve_opt
    } else {
        opt
    };
    let out = exact::solve_first(world, &model, index, effective_opt, None)?;
    let instance = out.instance.map(|states| Instance {
        trace_length: states.len() as i32,
        loop_state: out.loop_state,
        states,
    });
    if do_verify && out.sat {
        if let Some(ref inst) = instance {
            eval::verify_instance(&model, index, inst, opt).map_err(|e| {
                AlloyError::new(
                    ErrorKind::Other,
                    None,
                    format!("instance verification failed: {e}"),
                )
            })?;
        }
    }
    let instance = if opt.want_instance { instance } else { None };
    Ok(Solution {
        sat: out.sat,
        temporal: out.temporal,
        min_trace: out.min_trace,
        max_trace: out.max_trace,
        translate_ms: out.translate_ms,
        solve_ms: out.solve_ms,
        stats: Stats {
            primary_vars: out.primary_vars as i64,
            vars: out.vars as i64,
            clauses: out.clauses,
        },
        instance,
        xml_data: out.xml_data,
    })
}

/// Number of solutions of command `index` (Kodkod `solveAll` semantics, no symmetry breaking), counted up to `limit`:
/// `(count, capped)`. Temporal problems follow Pardinus `next()` semantics (static relations fixed from first
/// solution, distinct canonical lassos enumerated over increasing trace lengths).
pub fn count_solutions(
    world: &World,
    index: usize,
    opt: &Options,
    limit: u32,
) -> Result<(u32, bool), AlloyError> {
    let model = sema::build(&world.modules)?;
    let mut copt = opt.clone();
    copt.symmetry = 0;
    let (_cx, mut p) = exact::prepare(world, &model, index, &copt)?;
    let kerr = |e: String| AlloyError::new(ErrorKind::Other, None, e);
    if !p.options.temporal {
        pardinus::translator::count_all(&mut p, limit).map_err(kerr)
    } else {
        pardinus::temporal::count_solutions(&mut p, limit).map_err(kerr)
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

    fn run_opt(src: &str, idx: usize, opt: &Options) -> Result<Solution, AlloyError> {
        static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(2000);
        let n = N.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let dir =
            std::env::temp_dir().join(format!("alloy_rs_opts_{}_{}", std::process::id(), n));
        std::fs::create_dir_all(&dir).unwrap();
        let f = dir.join("o.als");
        std::fs::write(&f, src).unwrap();
        let world = alloy_core::parse_everything_from_file(&f)?;
        execute_command(&world, idx, opt)
    }

    #[test]
    fn options_skolem_depth_symmetry_and_unrolls_are_wired() {
        // skolem_depth = -1 disables skolem constants (so no `skolem:$x` in instance)
        let src_sk = "sig A {}\nrun { some a: A | some a } for 2\n";
        let s0 = run_opt(src_sk, 0, &Options::default()).unwrap();
        assert!(s0.sat);
        assert!(s0.instance().unwrap().states[0].keys().any(|k| k.starts_with("skolem:")));
        let mut opt_nosk = Options::default();
        opt_nosk.skolem_depth = -1;
        let s1 = run_opt(src_sk, 0, &opt_nosk).unwrap();
        assert!(s1.sat);
        assert!(!s1.instance().unwrap().states[0].keys().any(|k| k.starts_with("skolem:")));

        // symmetry = 0 works cleanly
        let mut opt_nosym = Options::default();
        opt_nosym.symmetry = 0;
        assert!(run_opt(src_sk, 0, &opt_nosym).unwrap().sat);

        // unrolls < 0 rejects recursive preds; unrolls >= 0 unrolls up to bound
        let src_rec = "pred p[n: Int] { n > 0 => p[minus[n, 1]] else n = 0 }\nrun { p[1] } for 4 int\n";
        assert!(run_opt(src_rec, 0, &Options::default()).is_err());
        let mut opt_unroll = Options::default();
        opt_unroll.unrolls = 2;
        assert!(run_opt(src_rec, 0, &opt_unroll).unwrap().sat);
    }
}
