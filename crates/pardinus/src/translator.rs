//! Port of `kodkod.engine.fol2sat.Translator` (static problems, no logging, not incremental) plus
//! `PardinusBounds.resolve` (symbolic bounds) and `Translation.interpret`.

use crate::annotate::annotate;
use crate::ast::*;
use crate::bool::*;
use crate::cnf::{self, CnfSink};
use crate::fol2bool::{Fol2Bool, Leaf, Val};
use crate::instance::*;
use crate::replace::{inline_predicates, skolemize, SkolemInfo};
use crate::symmetry::Breaker;
use std::collections::HashMap;

/// Result of a translation: the final bounds (`completeBounds`), the primary variable ranges, the skolems, and
/// whether the circuit was constant.
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

/// `Translator.translate` of a static problem (also the expansion of a temporal one: `options.temporal` then only
/// keeps skolems out of symmetry breaking).
pub fn translate_expanded(p: &mut Problem, sink: &mut dyn CnfSink) -> Result<Translation, String> {
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
    let sbp = breaker.generate_sbp(ast, &bounds, &leaf, &mut factory, &opt)?;
    let vars = leaf.vars.clone();
    let mut trivial = None;
    if circuit == TRUE || circuit == FALSE {
        cnf::translate_constant(circuit, sink);
        trivial = Some(circuit == TRUE);
    } else {
        let root = factory.and(circuit, sbp);
        let max_primary = factory.max_variable();
        if root == TRUE || root == FALSE {
            cnf::translate_constant(root, sink);
            trivial = Some(root == TRUE);
        } else {
            cnf::translate(&factory, root, max_primary, sink);
        }
    }
    // completeBounds
    if bounds.ints.is_empty() {
        bounds.ints = original_bounds.ints.clone();
    }
    for r in original_bounds.relations() {
        if !bounds.has_concrete(r) {
            let (l, u) = (original_bounds.lower[&r].clone(), original_bounds.upper[&r].clone());
            bounds.bound(r, l, u);
        }
    }
    let num_primary = if trivial.is_some() { 0 } else { nvars };
    Ok(Translation { bounds, vars: if trivial.is_some() { Vec::new() } else { vars }, num_primary, skolems, trivial })
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
