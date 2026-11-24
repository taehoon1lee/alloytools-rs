//! Port of `kodkod.engine.fol2sat.Translator` (static problems, no logging, not incremental) plus
//! `PardinusBounds.resolve` (symbolic bounds) and `Translation.interpret`.

use crate::annotate::annotate;
use crate::ast::*;
use crate::bool::*;
use crate::cnf::{self, ClauseBuffer, CnfSink};
use crate::fol2bool::{Fol2Bool, Leaf, Val};
use crate::instance::*;
use crate::replace::{inline_predicates, skolemize, SkolemInfo};
use crate::symmetry::{Breaker, SbpOrder};
use satsolver::{BatSat, SatSolver};
use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

/// Result of a translation: the final bounds (`completeBounds`), the primary variable ranges, the skolems, and
/// whether the circuit was constant.
#[derive(Clone, Debug)]
pub struct Translation {
    pub bounds: Bounds,
    /// relation -> first primary variable (relations with variables only), allocation order
    pub vars: Vec<(N, i32, i32)>,
    pub num_primary: i32,
    pub skolems: Vec<SkolemInfo>,
    /// `Some(value)` when the circuit was a constant (trivial translation)
    pub trivial: Option<bool>,
}

/// Evaluates a (constant) expression over the given relation tuples (`Evaluator` / `Translator.evaluate`).
pub fn evaluate(ast: &Ast, e: N, n: u32, rels: HashMap<N, TupleSet>, ints: &std::collections::BTreeMap<i32, TupleSet>, bitwidth: i32) -> Result<TupleSet, String> {
    let ann = annotate(ast, e);
    let leaf = Leaf::constant(n, rels, ints.clone());
    let mut f = Factory::new(0, 3, bitwidth, false);
    let mut t = Fol2Bool::new(ast, &ann, &leaf, &mut f, false);
    match t.translate(e)? {
        Val::M(m) => Ok(TupleSet::new(ast.arity(e), m.cells.keys().copied().collect())),
        _ => Err("symbolic bound is not an expression".into()),
    }
}

/// Relations of an expression in DFS order (`RelationCollector`; the Java set is a HashSet).
fn relations_of(ast: &Ast, e: N, out: &mut Vec<N>) {
    match ast.get(e) {
        Node::Rel(_) => {
            if !out.contains(&e) {
                out.push(e)
            }
        }
        _ => {
            for c in crate::annotate::children(ast, e) {
                relations_of(ast, c, out);
            }
        }
    }
}

/// `PardinusBounds.resolve(reporter)`: turns the symbolic bounds into concrete ones (in resolution order) and
/// returns the extra constraints.
pub fn resolve(ast: &mut Ast, b: &mut Bounds, bitwidth: i32) -> Result<N, String> {
    let mut xtra: Vec<N> = Vec::new();
    let rs: Vec<N> = b.symb.iter().map(|x| x.0).collect();
    for r in rs {
        resolve_rel(ast, b, r, &mut xtra, bitwidth)?;
    }
    Ok(ast.and_all(&xtra))
}

fn resolve_rel(ast: &mut Ast, b: &mut Bounds, rel: N, out: &mut Vec<N>, bitwidth: i32) -> Result<(), String> {
    let pos = match b.symb.iter().position(|x| x.0 == rel) {
        Some(p) => p,
        None => return Ok(()),
    };
    let (_, lo, hi) = b.symb[pos];
    // deps: relations of lower.union(upper)
    let mut deps = Vec::new();
    relations_of(ast, lo, &mut deps);
    relations_of(ast, hi, &mut deps);
    for d in deps {
        resolve_rel(ast, b, d, out, bitwidth)?;
    }
    let pos = b.symb.iter().position(|x| x.0 == rel).unwrap();
    let pre = b.lower.get(&rel).cloned().zip(b.upper.get(&rel).cloned());
    if let Some((p1, p2)) = &pre {
        if b.has_concrete(rel) && p1.len() == p2.len() {
            b.symb.remove(pos);
            return Ok(());
        }
    }
    let n = b.universe_size();
    let lowers: HashMap<N, TupleSet> = b.lower.clone();
    let uppers: HashMap<N, TupleSet> = b.upper.clone();
    let low_low = evaluate(ast, lo, n, lowers.clone(), &b.ints, bitwidth)?;
    let upp_upp = evaluate(ast, hi, n, uppers.clone(), &b.ints, bitwidth)?;
    if !upp_upp.contains_all(&low_low) {
        return Err("Resolved lower larger than resolver upper.".into());
    }
    b.bound(rel, low_low.clone(), upp_upp.clone());
    let low_upp = evaluate(ast, lo, n, uppers.clone(), &b.ints, bitwidth)?;
    let upp_low = evaluate(ast, hi, n, lowers, &b.ints, bitwidth)?;
    let mut constr: Option<N> = None;
    if low_low.len() != low_upp.len() && !matches!(ast.get(lo), Node::ConstE(ConstE::None)) {
        let x = ast.in_(lo, rel);
        constr = Some(match constr {
            None => x,
            Some(c) => ast.binf(c, FOp::And, x),
        });
    }
    if upp_low.len() != upp_upp.len() {
        let x = ast.in_(rel, hi);
        constr = Some(match constr {
            None => x,
            Some(c) => ast.binf(c, FOp::And, x),
        });
    }
    let pos = b.symb.iter().position(|x| x.0 == rel).unwrap();
    b.symb.remove(pos);
    if let Some(mut c) = constr {
        // a constraint over variable relations holds in every state
        if is_temporal_node(ast, c) {
            c = ast.add(Node::UTempF(crate::ast::TOp::Always, c));
        }
        out.push(c);
    }
    Ok(())
}

/// `TemporalTranslator.isTemporal`
fn is_temporal_node(ast: &Ast, n: N) -> bool {
    match ast.get(n) {
        Node::UTempF(..) | Node::BTempF(..) | Node::TempE(..) => true,
        Node::Rel(ri) => ri.var,
        _ => crate::annotate::children(ast, n).into_iter().any(|c| is_temporal_node(ast, c)),
    }
}

/// `Translator.translate(formula, bounds, options)` + `Bool2CNFTranslator` into `sink`.
pub fn translate(p: &mut Problem, sink: &mut dyn CnfSink) -> Result<Translation, String> {
    if p.options.temporal {
        return Err("temporal problems are solved with temporal::solve".into());
    }
    translate_expanded(p, sink)
}

/// Intermediate result of Stage 1 translation (up to `Fol2Bool`, before SBP/CNF).
pub struct Circuit {
    pub sbp_bounds: Bounds,
    pub complete_bounds: Bounds,
    pub vars: Vec<(N, i32, i32)>,
    pub nvars: i32,
    pub skolems: Vec<SkolemInfo>,
    pub factory: Factory,
    pub breaker: Breaker,
    pub leaf: Leaf,
    pub circuit: BV,
    pub options: Options,
}

impl Circuit {
    pub fn into_translation(self, trivial: Option<bool>) -> Translation {
        let is_triv = trivial.is_some();
        Translation {
            bounds: self.complete_bounds,
            vars: if is_triv { Vec::new() } else { self.vars },
            num_primary: if is_triv { 0 } else { self.nvars },
            skolems: self.skolems,
            trivial,
        }
    }
}

/// Stage 1: symbolic resolution -> annotate -> matrix symmetries -> inline -> skolemize -> `Fol2Bool`.
pub fn translate_circuit(p: &mut Problem) -> Result<Circuit, String> {
    let opt = p.options.clone();
    let ast = &mut p.ast;
    let mut bounds = p.bounds.clone();
    // constructor: symbForm = TRUE.and(bounds.resolve()); originalFormula = formula.and(symbForm)
    let resolved = resolve(ast, &mut bounds, opt.bitwidth)?;
    let tru = ast.tru();
    let symb_form = ast.binf(tru, FOp::And, resolved);
    let original = ast.binf(p.goal, FOp::And, symb_form);
    let original_bounds = bounds.clone();
    // translate()
    let ann = annotate(ast, original);
    let rels = ann.relations(ast);
    bounds.conc.retain(|r| rels.contains(r));
    bounds.lower.retain(|r, _| rels.contains(r));
    bounds.upper.retain(|r, _| rels.contains(r));
    if !ann.uses_ints(ast) {
        bounds.ints.clear();
    }
    let mut breaker = Breaker::new(&bounds, ast);
    // optimizeFormulaAndBounds
    let (totals, acyclics) = ann.predicates(ast);
    let true_preds = breaker.break_matrix_symmetries(ast, &mut bounds, &totals, &acyclics);
    let inlined = inline_predicates(ast, &ann, &true_preds)?;
    let ann2 = annotate(ast, inlined);
    let (root, skolems) = if opt.skolem_depth >= 0 {
        let (r, sk) = skolemize(ast, &ann2, &mut bounds, &opt)?;
        (r, sk)
    } else {
        (inlined, Vec::new())
    };
    let ann3 = if root == ann2.node { ann2 } else { annotate(ast, root) };
    // toBoolean
    let (leaf, nvars) = Leaf::exact(&bounds)?;
    let mut factory = Factory::new(nvars, opt.sharing, opt.bitwidth, opt.no_overflow);
    let circuit = {
        let mut t = Fol2Bool::new(ast, &ann3, &leaf, &mut factory, false);
        t.stop = opt.stop.clone();
        match t.translate(ann3.node)? {
            Val::B(b) => b,
            _ => return Err("goal is not a formula".into()),
        }
    };
    let vars = leaf.vars.clone();
    // completeBounds
    let mut complete_bounds = bounds.clone();
    if complete_bounds.ints.is_empty() {
        complete_bounds.ints = original_bounds.ints.clone();
    }
    for r in original_bounds.relations() {
        if !complete_bounds.has_concrete(r) {
            let (l, u) = (original_bounds.lower[&r].clone(), original_bounds.upper[&r].clone());
            complete_bounds.bound(r, l, u);
        }
    }
    Ok(Circuit {
        sbp_bounds: bounds,
        complete_bounds,
        vars,
        nvars,
        skolems,
        factory,
        breaker,
        leaf,
        circuit,
        options: opt,
    })
}

/// Stage 2: generates SBP under `order` and translates `circuit & sbp` to CNF into `sink`.
/// Returns `(trivial, root_bv)`.
pub fn emit_cnf(ast: &Ast, c: &mut Circuit, order: SbpOrder, sink: &mut dyn CnfSink) -> Result<(Option<bool>, BV), String> {
    if c.circuit == TRUE || c.circuit == FALSE {
        cnf::translate_constant(c.circuit, sink);
        return Ok((Some(c.circuit == TRUE), c.circuit));
    }
    let sbp = c.breaker.generate_sbp(ast, &c.sbp_bounds, &c.leaf, &mut c.factory, &c.options, order)?;
    let root = c.factory.and(c.circuit, sbp);
    if root == TRUE || root == FALSE {
        cnf::translate_constant(root, sink);
        Ok((Some(root == TRUE), root))
    } else {
        let max_primary = c.factory.max_variable();
        cnf::translate(&c.factory, root, max_primary, sink);
        Ok((None, root))
    }
}

/// `Translator.translate` of a static problem (also the expansion of a temporal one: `options.temporal` then only
/// keeps skolems out of symmetry breaking). Uses `SbpOrder::JavaOrder`.
pub fn translate_expanded(p: &mut Problem, sink: &mut dyn CnfSink) -> Result<Translation, String> {
    let mut c = translate_circuit(p)?;
    let (trivial, _) = emit_cnf(&p.ast, &mut c, SbpOrder::JavaOrder, sink)?;
    Ok(c.into_translation(trivial))
}

/// Result of `solve_portfolio`.
pub struct Solved {
    pub sat: bool,
    pub translation: Translation,
    /// 1-based assignment for `1..=num_primary` (empty if UNSAT or trivial).
    pub model: Vec<bool>,
    pub vars: i32,
    pub clauses: i64,
    pub translate_ms: f64,
    pub solve_ms: f64,
}

fn solve_buffer_with(
    factory: &Factory,
    circuit: BV,
    buf: &ClauseBuffer,
    max_primary: i32,
    luby: bool,
    rnd: f64,
    seed: u32,
    pol: Option<bool>,
    bin_watches: bool,
    conflict_limit: Option<u64>,
    time_limit: Option<Duration>,
    stop: Option<Arc<AtomicBool>>,
) -> Result<Option<(bool, Vec<bool>, i32, i64)>, String> {
    let mut sat = BatSat::configured(luby, rnd, seed, pol);
    sat.set_binary_watches(bin_watches);
    if let Some(lim) = conflict_limit {
        sat.set_conflict_limit(Some(lim));
    }
    if let Some(tl) = time_limit {
        sat.set_time_limit(Some(tl));
    }
    if let Some(st) = stop {
        sat.set_stop_flag(st);
    }
    if !buf.feed_to(&mut sat) {
        return Ok(Some((false, Vec::new(), buf.num_vars, buf.num_clauses)));
    }
    let frozen: Vec<u32> = (1..=max_primary as u32).collect();
    if std::env::var("KSAT_PRIO").is_ok() {
        sat.set_priority(&frozen);
    }
    sat.set_simplify(&frozen);
    match sat.solve() {
        Some(false) => Ok(Some((false, Vec::new(), buf.num_vars, buf.num_clauses))),
        Some(true) => {
            cnf::verify_cnf_model(&buf.clauses, &|v| sat.value_of(v))?;
            if !factory.eval_bv(circuit, &|v| sat.value_of(v))? {
                return Err("circuit verification failed: model evaluates circuit to false".into());
            }
            let mut model = vec![false; max_primary as usize + 1];
            for v in 1..=max_primary as u32 {
                model[v as usize] = sat.value_of(v);
            }
            Ok(Some((true, model, buf.num_vars, buf.num_clauses)))
        }
        None => Ok(None),
    }
}

fn build_root_for_order(ast: &Ast, circ: &mut Circuit, order: SbpOrder) -> Result<BV, String> {
    if order == SbpOrder::NoSbp {
        return Ok(circ.circuit);
    }
    let sbp = circ.breaker.generate_sbp(ast, &circ.sbp_bounds, &circ.leaf, &mut circ.factory, &circ.options, order)?;
    Ok(circ.factory.and(circ.circuit, sbp))
}

/// Builds the boolean circuit once, branches into portfolio SBP/BatSat configs, and verifies any SAT model
/// against both the pre-BVE CNF and the SBP-free original circuit.
pub fn solve_portfolio(p: &mut Problem) -> Result<Solved, String> {
    let t_start = Instant::now();
    let mut circ = translate_circuit(p)?;
    if p.options.stop.as_ref().map_or(false, |s| s.load(Ordering::Relaxed)) {
        return Err("solver interrupted".into());
    }
    if circ.circuit == TRUE || circ.circuit == FALSE {
        let sat = circ.circuit == TRUE;
        let translate_ms = t_start.elapsed().as_secs_f64() * 1000.0;
        return Ok(Solved {
            sat,
            translation: circ.into_translation(Some(sat)),
            model: Vec::new(),
            vars: 0,
            clauses: 0,
            translate_ms,
            solve_ms: 0.0,
        });
    }
    let max_primary = circ.factory.max_variable();
    let cores = std::thread::available_parallelism().map_or(1, |n| n.get());

    if cores < 2 {
        let root0 = build_root_for_order(&p.ast, &mut circ, SbpOrder::JavaOrder)?;
        if root0 == FALSE {
            return Ok(Solved {
                sat: false,
                translation: circ.into_translation(Some(false)),
                model: Vec::new(),
                vars: 0,
                clauses: 0,
                translate_ms: t_start.elapsed().as_secs_f64() * 1000.0,
                solve_ms: 0.0,
            });
        }
        if root0 == TRUE {
            if !circ.factory.eval_bv(circ.circuit, &|_| false)? {
                return Err("circuit verification failed on trivial root".into());
            }
            return Ok(Solved {
                sat: true,
                translation: circ.into_translation(Some(true)),
                model: Vec::new(),
                vars: 0,
                clauses: 0,
                translate_ms: t_start.elapsed().as_secs_f64() * 1000.0,
                solve_ms: 0.0,
            });
        }
        let mut buf0 = ClauseBuffer::new();
        cnf::translate(&circ.factory, root0, max_primary, &mut buf0);
        let translate_ms = t_start.elapsed().as_secs_f64() * 1000.0;
        let t_solve = Instant::now();
        if let Some((sat, model, vars, clauses)) = solve_buffer_with(
            &circ.factory,
            circ.circuit,
            &buf0,
            max_primary,
            false,
            0.0,
            0,
            Some(true),
            true,
            Some(2_000),
            Some(Duration::from_millis(50)),
            None,
        )? {
            return Ok(Solved {
                sat,
                translation: circ.into_translation(None),
                model,
                vars,
                clauses,
                translate_ms,
                solve_ms: t_solve.elapsed().as_secs_f64() * 1000.0,
            });
        }
        let mut buf_nosbp = ClauseBuffer::new();
        cnf::translate(&circ.factory, circ.circuit, max_primary, &mut buf_nosbp);
        if let Some((sat, model, vars, clauses)) = solve_buffer_with(
            &circ.factory,
            circ.circuit,
            &buf_nosbp,
            max_primary,
            false,
            0.0,
            0,
            None,
            false,
            None,
            Some(Duration::from_millis(1_000)),
            None,
        )? {
            return Ok(Solved {
                sat,
                translation: circ.into_translation(None),
                model,
                vars,
                clauses,
                translate_ms,
                solve_ms: t_solve.elapsed().as_secs_f64() * 1000.0,
            });
        }
        let (sat, model, vars, clauses) = solve_buffer_with(
            &circ.factory,
            circ.circuit,
            &buf0,
            max_primary,
            false,
            0.0,
            0,
            None,
            true,
            None,
            None,
            None,
        )?
        .ok_or("solver interrupted")?;
        return Ok(Solved {
            sat,
            translation: circ.into_translation(None),
            model,
            vars,
            clauses,
            translate_ms,
            solve_ms: t_solve.elapsed().as_secs_f64() * 1000.0,
        });
    }

    const CONFIGS: [(SbpOrder, bool, f64, u32, Option<bool>); 10] = [
        (SbpOrder::JavaOrder, false, 0.0, 0, Some(true)),
        (SbpOrder::NoSbp, true, 0.0, 0, Some(true)),
        // Fixed negative polarity here pairs with the three Some(true) configs for 4-thread diversity.
        (SbpOrder::ArityDecl, true, 0.0, 0, Some(false)),
        (SbpOrder::DeclOrder, true, 0.0, 0, Some(true)),
        (SbpOrder::NoSbp, false, 0.0, 0, None),
        (SbpOrder::JavaOrder, true, 0.0, 0, None),
        (SbpOrder::ArityDecl, true, 0.0, 0, Some(true)),
        (SbpOrder::JavaOrder, false, 0.0, 0, None),
        (SbpOrder::ArityDecl, false, 0.0, 0, None),
        (SbpOrder::JavaOrder, false, 0.01, 7, None),
    ];
    let selected: Vec<usize> = match std::env::var("KSAT_CONFIGS") {
        Ok(v) => v.split(',').filter_map(|x| x.trim().parse().ok()).filter(|i| *i < CONFIGS.len()).collect(),
        Err(_) => (0..CONFIGS.len().min(cores.max(2)).min(4)).collect(),
    };
    if selected.is_empty() {
        return Err("no solver configuration selected".into());
    }
    let override_order = std::env::var("KSAT_ORDER").ok().and_then(|v| match v.trim() {
        "0" => Some(SbpOrder::JavaOrder),
        "1" => Some(SbpOrder::ArityDecl),
        "2" => Some(SbpOrder::DeclOrder),
        _ => None,
    });
    let effective_order = |order: SbpOrder| match (override_order, order) {
        (Some(o), x) if x != SbpOrder::NoSbp => o,
        (_, x) => x,
    };

    // Pre-build SBP roots sequentially on circ.factory (JavaOrder first to preserve exact gate state).
    let mut roots: Vec<(SbpOrder, BV)> = Vec::new();
    let has_java = selected.iter().any(|&ci| effective_order(CONFIGS[ci].0) == SbpOrder::JavaOrder);
    if has_java {
        roots.push((SbpOrder::JavaOrder, build_root_for_order(&p.ast, &mut circ, SbpOrder::JavaOrder)?));
    }
    for &ci in &selected {
        let ord = effective_order(CONFIGS[ci].0);
        if !roots.iter().any(|(o, _)| *o == ord) {
            roots.push((ord, build_root_for_order(&p.ast, &mut circ, ord)?));
        }
    }
    for &(_, root) in &roots {
        if root == FALSE {
            return Ok(Solved {
                sat: false,
                translation: circ.into_translation(Some(false)),
                model: Vec::new(),
                vars: 0,
                clauses: 0,
                translate_ms: t_start.elapsed().as_secs_f64() * 1000.0,
                solve_ms: 0.0,
            });
        }
        if root == TRUE {
            if !circ.factory.eval_bv(circ.circuit, &|_| false)? {
                return Err("circuit verification failed on trivial root".into());
            }
            return Ok(Solved {
                sat: true,
                translation: circ.into_translation(Some(true)),
                model: Vec::new(),
                vars: 0,
                clauses: 0,
                translate_ms: t_start.elapsed().as_secs_f64() * 1000.0,
                solve_ms: 0.0,
            });
        }
    }

    let translate_ms = t_start.elapsed().as_secs_f64() * 1000.0;
    let t_solve = Instant::now();
    let stop = Arc::new(AtomicBool::new(false));
    let (tx, rx) = std::sync::mpsc::channel::<(usize, Result<Option<(bool, Vec<bool>, i32, i64)>, String>)>();
    let who = std::env::var("KSAT_WHO").is_ok();
    let factory = &circ.factory;
    let circuit = circ.circuit;
    let ext_stop = p.options.stop.as_deref();

    let winner = std::thread::scope(|scope| {
        for &ci in &selected {
            let (raw_ord, luby, rnd, seed, pol) = CONFIGS[ci];
            let order = effective_order(raw_ord);
            let root = roots.iter().find(|(o, _)| *o == order).unwrap().1;
            let tx = tx.clone();
            let stop = stop.clone();
            scope.spawn(move || {
                if stop.load(Ordering::Relaxed) || ext_stop.map_or(false, |s| s.load(Ordering::Relaxed)) {
                    let _ = tx.send((ci, Ok(None)));
                    return;
                }
                let mut buf = ClauseBuffer::new();
                cnf::translate(factory, root, max_primary, &mut buf);
                let r = solve_buffer_with(
                    factory,
                    circuit,
                    &buf,
                    max_primary,
                    luby,
                    rnd,
                    seed,
                    pol,
                    order != SbpOrder::NoSbp,
                    None,
                    None,
                    Some(stop),
                );
                let _ = tx.send((ci, r));
            });
        }
        drop(tx);
        let mut answer: Option<Result<(bool, Vec<bool>, i32, i64), String>> = None;
        for (ci, r) in rx.iter() {
            match r {
                Ok(Some(res)) => {
                    if answer.is_none() {
                        if who {
                            eprintln!("portfolio: config {ci} answered after {:?}", t_solve.elapsed());
                        }
                        answer = Some(Ok(res));
                        stop.store(true, Ordering::Relaxed);
                    }
                }
                Ok(None) => {}
                Err(e) => {
                    answer = Some(Err(e));
                    stop.store(true, Ordering::Relaxed);
                }
            }
        }
        answer.unwrap_or_else(|| Err("no solver configuration finished".to_string()))
    })?;

    let solve_ms = t_solve.elapsed().as_secs_f64() * 1000.0;
    let (sat, model, vars, clauses) = winner;
    Ok(Solved {
        sat,
        translation: circ.into_translation(None),
        model,
        vars,
        clauses,
        translate_ms,
        solve_ms,
    })
}

/// Counts solutions (Kodkod `solveAll` semantics without lex-leader SBP) up to `limit`.
pub fn count_all(p: &mut Problem, limit: u32) -> Result<(u32, bool), String> {
    count_projected(p, limit, None)
}

/// Like [`count_all`], projecting onto primary variables of `only` if given.
pub fn count_projected(p: &mut Problem, limit: u32, only: Option<&[N]>) -> Result<(u32, bool), String> {
    p.options.symmetry = 0;
    let circ = translate_circuit(p)?;
    if circ.circuit == FALSE {
        return Ok((0, false));
    }
    let primaries: Vec<u32> = match only {
        None => (1..=circ.nvars as u32).collect(),
        Some(rels) => {
            let mut pvars = Vec::new();
            let mut seen = Vec::new();
            for &r in rels {
                if !seen.contains(&r) {
                    seen.push(r);
                    if let Some(&(_, first, count)) = circ.vars.iter().find(|&&(vr, _, _)| vr == r) {
                        for v in first..first + count {
                            pvars.push(v as u32);
                        }
                    }
                }
            }
            pvars.sort_unstable();
            pvars.dedup();
            pvars
        }
    };
    if circ.circuit == TRUE {
        let bits = primaries.len() as u32;
        if bits >= 32 {
            return Ok((limit, true));
        }
        let total = 1u64 << bits;
        return if total > limit as u64 {
            Ok((limit, true))
        } else {
            Ok((total as u32, false))
        };
    }
    let max_primary = circ.factory.max_variable();
    let mut sat = BatSat::configured(false, 0.0, 0, Some(true));
    let mut sink = cnf::SolverSink::new(&mut sat);
    cnf::translate(&circ.factory, circ.circuit, max_primary, &mut sink);
    let mut n = 0u32;
    loop {
        if sat.solve() != Some(true) {
            return Ok((n, false));
        }
        if n >= limit {
            return Ok((n, true));
        }
        n += 1;
        let block: Vec<i32> = primaries.iter().map(|&v| if sat.value_of(v) { -(v as i32) } else { v as i32 }).collect();
        if block.is_empty() || !sat.add_clause(&block) {
            return Ok((n, false));
        }
    }
}

/// First model without symmetry breaking and with lexicographically smallest assignment over `minimize` relations
/// (using `solve_assuming`, matching MiniSat false-first behavior).
pub fn first_instance(p: &mut Problem, minimize: &[N]) -> Result<Option<HashMap<N, TupleSet>>, String> {
    p.options.symmetry = 0;
    let circ = translate_circuit(p)?;
    if circ.circuit == FALSE {
        return Ok(None);
    }
    if circ.circuit == TRUE {
        let tr = circ.into_translation(Some(true));
        return Ok(Some(tr.interpret(&|_| false).into_iter().collect()));
    }
    let max_primary = circ.factory.max_variable();
    let mut sat = BatSat::configured(false, 0.0, 0, Some(false));
    let mut sink = cnf::SolverSink::new(&mut sat);
    cnf::translate(&circ.factory, circ.circuit, max_primary, &mut sink);
    let tr = circ.into_translation(None);
    let prio: Vec<u32> = (1..=tr.num_primary as u32).collect();
    sat.set_priority(&prio);
    if sat.solve() != Some(true) {
        return Ok(None);
    }
    let mut vars: Vec<u32> = Vec::new();
    for &r in minimize {
        if let Some(&(_, first, count)) = tr.vars.iter().find(|&&(vr, _, _)| vr == r) {
            for v in first..first + count {
                vars.push(v as u32);
            }
        }
    }
    vars.sort_unstable();
    vars.dedup();
    let mut fixed: Vec<i32> = Vec::new();
    for v in vars {
        if !sat.value_of(v) {
            fixed.push(-(v as i32));
            continue;
        }
        fixed.push(-(v as i32));
        if sat.solve_assuming(&fixed) != Some(true) {
            fixed.pop();
            fixed.push(v as i32);
            if sat.solve_assuming(&fixed) != Some(true) {
                return Ok(None);
            }
        }
    }
    let inst: HashMap<N, TupleSet> = tr.interpret(&|v| v > 0 && sat.value_of(v as u32)).into_iter().collect();
    Ok(Some(inst))
}

impl Translation {
    /// `Translation.interpret()`: relation -> tuple set under the model `value_of(var)`.
    pub fn interpret(&self, value_of: &dyn Fn(i32) -> bool) -> Vec<(N, TupleSet)> {
        let mut out = Vec::new();
        let first: HashMap<N, i32> = self.vars.iter().map(|(r, v, _)| (*r, *v)).collect();
        for r in self.bounds.relations() {
            let lower = &self.bounds.lower[&r];
            let mut idx = lower.idx.clone();
            if let Some(&min) = first.get(&r) {
                let mut lit = min;
                for &i in &self.bounds.upper[&r].idx {
                    if !lower.contains(i) {
                        if value_of(lit) {
                            idx.push(i);
                        }
                        lit += 1;
                    }
                }
            }
            out.push((r, TupleSet::new(lower.arity, idx)));
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_problem(sat_goal: bool) -> Problem {
        let mut ast = Ast::new();
        let r = ast.rel("R", 1);
        let a_some = ast.mult(Mult::Some, r);
        let a_no = ast.mult(Mult::No, r);
        let goal = if sat_goal {
            a_some
        } else {
            ast.binf(a_some, FOp::And, a_no)
        };
        let mut bounds = Bounds {
            atoms: vec!["A$0".into(), "A$1".into(), "A$2".into()],
            ..Default::default()
        };
        bounds.bound_upper(r, TupleSet::new(1, vec![0, 1, 2]));
        Problem { ast, bounds, options: Options::default(), goal }
    }

    #[test]
    fn solve_portfolio_verifies_sat_and_handles_unsat_and_trivial() {
        let mut p_sat = sample_problem(true);
        let s = solve_portfolio(&mut p_sat).unwrap();
        assert!(s.sat);
        let value = |v: i32| v > 0 && *s.model.get(v as usize).unwrap_or(&false);
        let inst: HashMap<N, TupleSet> = s.translation.interpret(&value).into_iter().collect();
        let r_node = N(0);
        assert!(!inst[&r_node].is_empty());

        let mut p_unsat = sample_problem(false);
        let u = solve_portfolio(&mut p_unsat).unwrap();
        assert!(!u.sat);

        // Trivial TRUE with unconstrained 2-element relation -> 2^2 = 4 solutions
        let mut ast = Ast::new();
        let r = ast.rel("R", 1);
        let goal = ast.eq(r, r);
        let mut bounds = Bounds { atoms: vec!["A$0".into(), "A$1".into()], ..Default::default() };
        bounds.bound_upper(r, TupleSet::new(1, vec![0, 1]));
        let mut p_triv = Problem { ast, bounds, options: Options::default(), goal };
        let st = solve_portfolio(&mut p_triv).unwrap();
        assert!(st.sat);
        assert_eq!(count_all(&mut p_triv, 100).unwrap(), (4, false));
        assert_eq!(count_all(&mut p_triv, 3).unwrap(), (3, true));
    }

    #[test]
    fn count_all_matches_non_trivial_problem() {
        let mut p = sample_problem(true);
        // 3 atoms, `some R` -> 2^3 - 1 = 7 solutions
        assert_eq!(count_all(&mut p, 100).unwrap(), (7, false));
        assert_eq!(count_all(&mut p, 5).unwrap(), (5, true));
    }
}
