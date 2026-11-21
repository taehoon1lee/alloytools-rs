//! Port of `CORE/translator/TranslateAlloyToKodkod.java` (the part that does not need integers):
//! relation bounds from the atom layout, sig and field constraints, and the translation of the
//! resolved expressions/formulas to Kodkod's relational logic.
//!
//! Java: `TranslateAlloyToKodkod.execute_command` builds `facts ∧ sigfacts ∧ sigconstraints` and
//! for `run` the command formula, for `check` its negation (`check` = facts ∧ ¬assertion).

use std::collections::HashMap;

use alloy_core::error::{AlloyError, ErrorKind};
use alloy_core::sema::{FieldId, LocalId, Model, RCommand, RDecl, RExpr, SigId, SigKind, SIG_INT, SIG_NONE, SIG_UNIV};
use alloy_core::syntax::{BinOp, Const, Mult, Quant, UnOp};
use kodkod::ast::{Const as KConst, Decl, Expr, Formula, IntCmp, IntExpr, Multiplicity, Quantifier};
use kodkod::instance::{Bounds, TupleSet, Universe};

use crate::scope::{compute_scopes, Layout};
use crate::Options;

/// A translated command: the bounds and the closed formula to solve.
pub struct Problem {
    pub bounds: Bounds,
    pub formula: Formula,
}

fn unsupported(msg: impl Into<String>) -> AlloyError {
    AlloyError::unsupported(msg)
}

fn other(msg: impl Into<String>) -> AlloyError {
    AlloyError::new(ErrorKind::Other, None, msg)
}

/// Max depth of nested predicate/function inlining (guards recursive definitions).
const MAX_CALL_DEPTH: usize = 40;

pub fn translate(model: &Model, cmd: &RCommand, opt: &Options) -> Result<Problem, AlloyError> {
    let _ = opt;
    let lay = compute_scopes(model, cmd)?;
    // Java always adds the integer atoms to the universe (bitwidth 4 unless the command says otherwise),
    // exact in the `Int` relation, so they cost no primary variables.
    let bitwidth = cmd.bitwidth.unwrap_or(4);
    let int_atoms = int_atom_names(bitwidth);
    let n_sig_atoms = lay.atoms.len() as u32;
    let mut atoms = lay.atoms.clone();
    atoms.extend(int_atoms.iter().cloned());
    let n_atoms = atoms.len() as u32;
    let universe = Universe::new(atoms).map_err(other)?;
    let mut bounds = Bounds::new(universe);
    bounds.bitwidth = bitwidth as u32;
    let int_tuples = TupleSet::from_tuples(1, (n_sig_atoms..n_atoms).map(|a| vec![a]));
    let int_rel = bounds
        .bound("Int", int_tuples.clone(), int_tuples)
        .map_err(other)?;
    bounds.ordered_atoms = (n_sig_atoms..n_atoms).collect();
    bounds.int_start = n_sig_atoms;
    bounds.int_min = if bitwidth > 0 { -(1i64 << (bitwidth - 1)) } else { 0 };

    // Relations of the sigs (Java `BoundsComputer.allocatePrimSig`): a sig without children is one relation; a sig
    // with children is the union of its children's expressions, plus a `_remainder` relation unless abstract.
    let mut sig_expr: Vec<Option<Expr>> = vec![None; model.sigs.len()];
    let mut disjoint: Vec<Formula> = Vec::new();
    for i in 0..model.sigs.len() {
        let s = &model.sigs[i];
        if s.kind == SigKind::User && s.parent.is_none() && s.subset_of.is_empty() {
            allocate_prim_sig(model, &lay, n_atoms, i as SigId, &mut bounds, &mut sig_expr, &mut disjoint)?;
        }
    }
    for (i, s) in model.sigs.iter().enumerate() {
        if s.kind == SigKind::User && !s.subset_of.is_empty() {
            let up = sig_upper(model, &lay, i as SigId, n_atoms)?;
            let lo = lay.lower(i as SigId);
            let id = bounds.bound(&s.label, unary(lo), unary(up)).map_err(other)?;
            sig_expr[i] = Some(Expr::Rel(id));
        }
    }
    // Relations of the fields: upper = owner × (type of the declaration).
    let mut field_rel: Vec<Option<u32>> = vec![None; model.fields.len()];
    let mut memo: Vec<Option<TupleSet>> = vec![None; model.fields.len()];
    for (fi, f) in model.fields.iter().enumerate() {
        let upper = field_upper(model, &lay, n_atoms, fi as FieldId, &mut memo, &mut Vec::new())?;
        let lower = TupleSet::empty(upper.arity);
        let id = bounds.bound(&f.label, lower, upper).map_err(other)?;
        field_rel[fi] = Some(id);
    }

    // Kodkod `SymmetryBreaker.breakTotalOrder`: `util/ordering`-style total orders over interchangeable atoms
    // get constant bounds (first = lowest atom, next = the natural chain) and their predicate becomes true.
    let mut pinned: std::collections::HashSet<(SigId, FieldId, FieldId)> = std::collections::HashSet::new();
    for (_, body) in model.sig_facts.iter().filter(|_| std::env::var("KNOPIN").is_err()) {
        pin_total_orders(body, &mut bounds, &sig_expr, &field_rel, &mut pinned);
    }

    let mut tr = Tr {
        pinned,
        model,
        lay: &lay,
        sig_expr,
        sig_disjoint: disjoint,
        int_rel,
        field_rel,
        locals: HashMap::new(),
        local_bound: HashMap::new(),
        pol: true,
        under_universal: false,
        n_atoms,
        local_arity: HashMap::new(),
        next_var: 0,
        depth: 0,
        bounds: &bounds,
    };

    let mut conjuncts = Vec::new();
    for f in &model.facts {
        conjuncts.push(tr.formula(&f.body)?);
    }
    for (sid, body) in &model.sig_facts {
        conjuncts.push(tr.formula(body)?);
        let _ = sid;
    }
    conjuncts.extend(tr.sig_constraints()?);
    conjuncts.extend(tr.field_constraints()?);

    // A `check` is solved negated: the command formula occurs in negative position, the facts in positive.
    tr.pol = !cmd.check;
    let command = tr.formula(&cmd.formula)?;
    conjuncts.push(if cmd.check { Formula::Not(Box::new(command)) } else { command });
    Ok(Problem {
        bounds,
        formula: Formula::And(conjuncts),
    })
}

/// Java `BoundsComputer.allocatePrimSig`.
fn allocate_prim_sig(
    model: &Model,
    lay: &Layout,
    n_atoms: u32,
    sid: SigId,
    bounds: &mut Bounds,
    sig_expr: &mut Vec<Option<Expr>>,
    disjoint: &mut Vec<Formula>,
) -> Result<Expr, AlloyError> {
    let sig = &model.sigs[sid as usize];
    let kids: Vec<SigId> = lay.children(sid).to_vec();
    let mut sum: Option<Expr> = None;
    for &k in &kids {
        let ce = allocate_prim_sig(model, lay, n_atoms, k, bounds, sig_expr, disjoint)?;
        sum = Some(match sum {
            None => ce,
            Some(prev) => {
                // subsigs are disjoint
                disjoint.push(Formula::Multiplicity(
                    Multiplicity::No,
                    Expr::Intersection(Box::new(prev.clone()), Box::new(ce.clone())),
                ));
                Expr::union(prev, ce)
            }
        });
    }
    let mut lower: Vec<u32> = lay.lower(sid);
    let mut upper: Vec<u32> = sig_upper(model, lay, sid, n_atoms)?;
    let e = match sum {
        None => {
            let id = bounds.bound(&sig.label, unary(lower), unary(upper)).map_err(other)?;
            Expr::Rel(id)
        }
        Some(sum) if sig.is_abstract => sum,
        Some(sum) => {
            // remainder: atoms known to be in a subsig are removed
            for &k in &kids {
                let known = lay.lower(k);
                lower.retain(|a| !known.contains(a));
                upper.retain(|a| !known.contains(a));
            }
            let id = bounds
                .bound(&format!("{}_remainder", sig.label), unary(lower), unary(upper))
                .map_err(other)?;
            Expr::union(sum, Expr::Rel(id))
        }
    };
    sig_expr[sid as usize] = Some(e.clone());
    Ok(e)
}

/// `(elem, first field, next field)` of `pred/totalOrder[elem, this.first, this.next]`.
fn total_order_key(args: &[RExpr]) -> Option<(SigId, FieldId, FieldId)> {
    let field_of = |e: &RExpr| match e {
        RExpr::Bin(BinOp::Join, a, b) => match (&**a, &**b) {
            (RExpr::Local(_), RExpr::Field(f)) => Some(*f),
            _ => None,
        },
        _ => None,
    };
    match args {
        [RExpr::Sig(e), f, n] => Some((*e, field_of(f)?, field_of(n)?)),
        _ => None,
    }
}

fn pin_total_orders(
    e: &RExpr,
    bounds: &mut Bounds,
    sig_rel: &[Option<Expr>],
    field_rel: &[Option<u32>],
    pinned: &mut std::collections::HashSet<(SigId, FieldId, FieldId)>,
) {
    match e {
        RExpr::Block(items) => {
            for i in items {
                pin_total_orders(i, bounds, sig_rel, field_rel, pinned);
            }
        }
        RExpr::Quant(Quant::All, _, body) => pin_total_orders(body, bounds, sig_rel, field_rel, pinned),
        RExpr::TotalOrder(args) => {
            let Some(key @ (elem, f1, f2)) = total_order_key(args) else { return };
            let (Some(Some(er)), Some(Some(r1)), Some(Some(r2))) =
                (sig_rel.get(elem as usize), field_rel.get(f1 as usize), field_rel.get(f2 as usize))
            else {
                return;
            };
            let Expr::Rel(er) = er else { return };
            let (er, r1, r2) = (*er as usize, *r1 as usize, *r2 as usize);
            if bounds.relations[r1].arity != 2 || bounds.relations[r2].arity != 3 {
                return;
            }
            let dom: Vec<u32> = bounds.relations[er].upper.tuples.iter().map(|t| t[0]).collect();
            // The owner (a `one` sig) must be a single atom: the first column of both fields.
            let owners: std::collections::BTreeSet<u32> = bounds.relations[r1].upper.tuples.iter().map(|t| t[0]).collect();
            if dom.is_empty() || owners.len() != 1 {
                return;
            }
            let o = *owners.iter().next().unwrap();
            if !dom.windows(2).all(|w| kodkod::translate::interchangeable(bounds, w[0], w[1])) {
                return;
            }
            let first_t = vec![o, dom[0]];
            let chain: std::collections::BTreeSet<Vec<u32>> = dom.windows(2).map(|w| vec![o, w[0], w[1]]).collect();
            if !bounds.relations[r1].upper.tuples.contains(&first_t)
                || !bounds.relations[r2].lower.tuples.is_subset(&chain)
                || !chain.is_subset(&bounds.relations[r2].upper.tuples)
            {
                return;
            }
            let upper_e = bounds.relations[er].upper.clone();
            bounds.relations[er].lower = upper_e;
            let first = TupleSet::from_tuples(2, std::iter::once(first_t));
            bounds.relations[r1].lower = first.clone();
            bounds.relations[r1].upper = first;
            let nx = TupleSet::from_tuples(3, chain.into_iter());
            bounds.relations[r2].lower = nx.clone();
            bounds.relations[r2].upper = nx;
            pinned.insert(key);
        }
        _ => {}
    }
}

/// Names of the integer atoms of a bitwidth: `-2^(b-1) ..= 2^(b-1)-1` (empty for bitwidth 0).
fn int_atom_names(bitwidth: i32) -> Vec<String> {
    if bitwidth <= 0 {
        return Vec::new();
    }
    let half = 1i64 << (bitwidth - 1);
    (-half..half).map(|v| v.to_string()).collect()
}

/// Numeric expressions (`Int` values rather than sets of atoms).
fn is_numeric(e: &RExpr) -> bool {
    match e {
        // `+`/`-` are always set union/difference (Java `ExprBinary` PLUS/MINUS type = union with common arity);
        // integer arithmetic is `IntPlus`/`IntMinus` (the `plus`/`minus` functions).
        RExpr::Block(items) if items.len() == 1 => is_numeric(&items[0]),
        _ => matches!(
            e,
            RExpr::Num(_)
                | RExpr::Const(Const::IntMin | Const::IntMax)
                | RExpr::Un(UnOp::Card | UnOp::IntCast | UnOp::Neg, _)
                | RExpr::Bin(BinOp::IntPlus | BinOp::IntMinus | BinOp::Mul | BinOp::Div | BinOp::Rem, _, _)
        ),
    }
}

fn unary(atoms: Vec<u32>) -> TupleSet {
    TupleSet::from_tuples(1, atoms.into_iter().map(|a| vec![a]))
}

/// Upper atoms of a sig, including subset sigs (`sig A in B + C` may take the atoms of B and C).
fn sig_upper(model: &Model, lay: &Layout, s: SigId, n_atoms: u32) -> Result<Vec<u32>, AlloyError> {
    let sig = &model.sigs[s as usize];
    if sig.kind == SigKind::Builtin {
        return Ok(match s {
            SIG_UNIV => (0..n_atoms).collect(),
            SIG_NONE => Vec::new(),
            SIG_INT => (lay.atoms.len() as u32..n_atoms).collect(),
            _ => return Err(unsupported(format!("builtin sig {} (strings/seq)", sig.label))),
        });
    }
    if !sig.subset_of.is_empty() {
        let mut out = Vec::new();
        for &t in &sig.subset_of {
            out.extend(sig_upper(model, lay, t, n_atoms)?);
        }
        out.sort_unstable();
        out.dedup();
        return Ok(out);
    }
    Ok(lay.upper(s))
}

/// Upper bound of a field: `owner × type(decl)` (Java `BoundsComputer` for fields). Fields used inside
/// other declarations contribute their own (memoized) upper bound, so `children: nodes -> nodes` works.
fn field_upper(
    model: &Model,
    lay: &Layout,
    n_atoms: u32,
    f: FieldId,
    memo: &mut Vec<Option<TupleSet>>,
    stack: &mut Vec<FieldId>,
) -> Result<TupleSet, AlloyError> {
    if let Some(t) = &memo[f as usize] {
        return Ok(t.clone());
    }
    if stack.contains(&f) {
        return Err(unsupported("recursive field declaration types"));
    }
    stack.push(f);
    let fld = &model.fields[f as usize];
    let owner = unary(sig_upper(model, lay, fld.owner, n_atoms)?);
    let mut env = HashMap::new();
    env.insert(LocalId::MAX, owner.clone());
    let decl = type_of(model, lay, n_atoms, &fld.decl, memo, stack, &mut env)?;
    stack.pop();
    let upper = owner.product(&decl);
    memo[f as usize] = Some(upper.clone());
    Ok(upper)
}

/// Type (upper-bound tuples) of a declaration expression, used for field bounds.
fn type_of(
    model: &Model,
    lay: &Layout,
    n_atoms: u32,
    e: &RExpr,
    memo: &mut Vec<Option<TupleSet>>,
    stack: &mut Vec<FieldId>,
    env: &mut HashMap<LocalId, TupleSet>,
) -> Result<TupleSet, AlloyError> {
    macro_rules! t {
        ($x:expr) => {
            type_of(model, lay, n_atoms, $x, memo, stack, env)?
        };
    }
    Ok(match e {
        RExpr::Sig(s) => unary(sig_upper(model, lay, *s, n_atoms)?),
        RExpr::Field(f) => field_upper(model, lay, n_atoms, *f, memo, stack)?,
        RExpr::Const(Const::Univ) => unary((0..n_atoms).collect()),
        RExpr::Const(Const::None) => TupleSet::empty(1),
        RExpr::Un(UnOp::Set | UnOp::One | UnOp::Lone | UnOp::Some, x) => t!(x),
        RExpr::Bin(BinOp::Plus, a, b) => t!(a).union(&t!(b)),
        RExpr::Bin(BinOp::Intersect, a, b) => {
            let (a, b) = (t!(a), t!(b));
            TupleSet {
                arity: a.arity,
                tuples: a.tuples.intersection(&b.tuples).cloned().collect(),
            }
        }
        RExpr::Bin(BinOp::Minus, a, _) => t!(a),
        RExpr::Bin(BinOp::Arrow(_, _), a, b) => t!(a).product(&t!(b)),
        RExpr::Bin(BinOp::Join, a, b) => join_ts(&t!(a), &t!(b))?,
        RExpr::Local(l) => match env.get(l).or_else(|| env.get(&LocalId::MAX)) {
            Some(t) => t.clone(),
            None => return Err(unsupported("unbound local in a declaration type")),
        },
        RExpr::Compr(decls, _) => {
            let mut acc: Option<TupleSet> = None;
            for d in decls {
                let b = t!(&d.bound);
                for v in &d.vars {
                    env.insert(*v, b.clone());
                    acc = Some(match acc {
                        None => b.clone(),
                        Some(a) => a.product(&b),
                    });
                }
            }
            acc.ok_or_else(|| other("empty comprehension"))?
        }
        RExpr::Call(fid, args) => {
            let f = &model.funcs[*fid as usize];
            for ((pid, _), a) in f.params.iter().zip(args) {
                let ty = t!(a);
                env.insert(*pid, ty);
            }
            t!(&f.body)
        }
        RExpr::Block(items) if items.len() == 1 => t!(&items[0]),
        RExpr::Choice(c) if c.len() == 1 => t!(&c[0]),
        RExpr::Choice(c) => {
            let mut acc: Option<TupleSet> = None;
            for x in c {
                let t = t!(x);
                acc = Some(match acc {
                    Some(a) if a.arity == t.arity => a.union(&t),
                    Some(a) => a,
                    None => t,
                });
            }
            acc.ok_or_else(|| other("empty choice"))?
        }
        RExpr::Const(Const::Iden) => {
            let all = unary((0..n_atoms).collect());
            TupleSet::from_tuples(2, all.tuples.iter().map(|t| vec![t[0], t[0]]))
        }
        RExpr::Const(Const::IntNext) | RExpr::Const(Const::IntMin) | RExpr::Const(Const::IntMax) => {
            let ints = unary(sig_upper(model, lay, SIG_INT, n_atoms)?);
            if matches!(e, RExpr::Const(Const::IntNext)) {
                ints.product(&ints)
            } else {
                ints
            }
        }
        RExpr::Num(_)
        | RExpr::Un(UnOp::Card | UnOp::IntCast | UnOp::Neg, _)
        | RExpr::Bin(BinOp::IntPlus | BinOp::IntMinus | BinOp::Mul | BinOp::Div | BinOp::Rem, _, _) => {
            unary(sig_upper(model, lay, SIG_INT, n_atoms)?)
        }
        RExpr::Un(UnOp::Closure | UnOp::ReflClosure, x) => {
            // Superset: any (first column, last column) pair.
            let a = t!(x);
            let mut out = TupleSet::empty(2);
            let firsts: std::collections::BTreeSet<u32> = a.tuples.iter().map(|t| t[0]).collect();
            let lasts: std::collections::BTreeSet<u32> = a.tuples.iter().map(|t| t[t.len() - 1]).collect();
            for &f in &firsts {
                for &l in &lasts {
                    out.tuples.insert(vec![f, l]);
                }
            }
            out
        }
        RExpr::Bin(BinOp::DomainRestrict, _, b) => t!(b),
        RExpr::Bin(BinOp::RangeRestrict, a, _) => t!(a),
        RExpr::Bin(BinOp::Override, a, b) => t!(a).union(&t!(b)),
        RExpr::Ite(_, a, b) => t!(a).union(&t!(b)),
        RExpr::Un(UnOp::Transpose, x) => {
            let a = t!(x);
            TupleSet::from_tuples(a.arity, a.tuples.iter().map(|t| t.iter().rev().copied().collect::<Vec<_>>()))
        }
        other_e => return Err(unsupported(format!("declaration type that is not a sig expression: {:.80}", format!("{other_e:?}")))),
    })
}

fn join_ts(a: &TupleSet, b: &TupleSet) -> Result<TupleSet, AlloyError> {
    if a.arity + b.arity < 3 {
        return Err(unsupported("join of two unary types in a declaration"));
    }
    let mut out = TupleSet::empty(a.arity + b.arity - 2);
    for ta in &a.tuples {
        for tb in &b.tuples {
            if ta[ta.len() - 1] == tb[0] {
                let mut t = ta[..ta.len() - 1].to_vec();
                t.extend_from_slice(&tb[1..]);
                out.tuples.insert(t);
            }
        }
    }
    Ok(out)
}

/// Expected type of an overloaded operand.
enum Exp {
    Any,
    /// Same arity and at least one common tuple.
    Same(TupleSet),
    /// Candidate's first column must hit these atoms (it is the right operand of a join).
    JoinRight(std::collections::BTreeSet<u32>),
    /// Candidate's last column must hit these atoms (it is the left operand of a join).
    JoinLeft(std::collections::BTreeSet<u32>),
}

struct Tr<'a> {
    pinned: std::collections::HashSet<(SigId, FieldId, FieldId)>,
    model: &'a Model,
    lay: &'a Layout,
    sig_expr: Vec<Option<Expr>>,
    /// `no (sum of earlier children & child)` formulas of the sig hierarchy.
    sig_disjoint: Vec<Formula>,
    /// The `Int` relation (exactly the integer atoms).
    int_rel: u32,
    field_rel: Vec<Option<u32>>,
    /// Alloy locals (quantifier variables, parameters, `let`s) -> kodkod expressions.
    locals: HashMap<LocalId, Expr>,
    /// Declared bound of quantifier variables (for typing overloaded names).
    local_bound: HashMap<LocalId, RExpr>,
    /// Polarity of the formula being translated (true = positive). A `check` is translated negated.
    pol: bool,
    /// An effectively universal quantifier encloses the current formula (Kodkod cannot skolemize below it).
    under_universal: bool,
    n_atoms: u32,
    /// Arity of kodkod variables (their domain's arity).
    local_arity: HashMap<u32, usize>,
    next_var: u32,
    depth: usize,
    bounds: &'a Bounds,
}

impl<'a> Tr<'a> {
    fn fresh(&mut self) -> u32 {
        self.next_var += 1;
        self.next_var - 1
    }

    fn sig_expr(&self, s: SigId) -> Result<Expr, AlloyError> {
        match s {
            SIG_UNIV => Ok(Expr::Const(KConst::Univ)),
            SIG_NONE => Ok(Expr::Const(KConst::None)),
            SIG_INT => Ok(Expr::Rel(self.int_rel)),
            _ => match self.sig_expr.get(s as usize).cloned().flatten() {
                Some(e) => Ok(e),
                None => Err(unsupported(format!("sig {} (integers/strings/seq)", self.model.sigs[s as usize].label))),
            },
        }
    }

    fn field_expr(&self, f: FieldId) -> Result<Expr, AlloyError> {
        self.field_rel[f as usize]
            .map(Expr::Rel)
            .ok_or_else(|| other("field without a relation"))
    }

    /// Static arity of a kodkod expression.
    fn arity(&self, e: &Expr) -> Result<usize, AlloyError> {
        Ok(match e {
            Expr::Rel(r) => self.bounds.rel(*r).arity,
            Expr::Var(v) => *self.local_arity.get(v).ok_or_else(|| other("unbound variable"))?,
            Expr::Const(KConst::Univ) | Expr::Const(KConst::None) => 1,
            Expr::Const(KConst::Iden) => 2,
            Expr::Literal(ts) => ts.arity,
            Expr::Union(a, _) | Expr::Intersection(a, _) | Expr::Difference(a, _) | Expr::Override(a, _) => self.arity(a)?,
            Expr::Join(a, b) => self.arity(a)? + self.arity(b)? - 2,
            Expr::Product(a, b) => self.arity(a)? + self.arity(b)?,
            Expr::Transpose(_) | Expr::Closure(_) | Expr::ReflexiveClosure(_) => 2,
            Expr::IntToExpr(_) => 1,
            Expr::IfThenElse(_, a, _) => self.arity(a)?,
            Expr::Comprehension(decls, _) => {
                let mut t = 0;
                for d in decls {
                    t += self.arity(&d.domain)?;
                }
                t
            }
        })
    }

    /// Static (upper-bound atom) type of an expression; `None` when it cannot be computed.
    fn ty(&self, e: &RExpr) -> Option<TupleSet> {
        let mut env: HashMap<LocalId, TupleSet> = HashMap::new();
        let mut pending: Vec<(&LocalId, &RExpr)> = self.local_bound.iter().collect();
        for _ in 0..3 {
            let mut rest = Vec::new();
            for (l, b) in pending {
                let mut memo = vec![None; self.model.fields.len()];
                match type_of(self.model, self.lay, self.n_atoms, b, &mut memo, &mut Vec::new(), &mut env) {
                    Ok(t) => {
                        env.insert(*l, t);
                    }
                    Err(_) => rest.push((l, b)),
                }
            }
            pending = rest;
            if pending.is_empty() {
                break;
            }
        }
        let mut memo = vec![None; self.model.fields.len()];
        type_of(self.model, self.lay, self.n_atoms, e, &mut memo, &mut Vec::new(), &mut env).ok()
    }

    /// Does candidate `c` fit the expected type?
    fn compatible(&self, c: &RExpr, exp: &Exp) -> bool {
        if matches!(exp, Exp::Any) {
            return true;
        }
        let Some(t) = self.ty(c) else { return true };
        match exp {
            Exp::Any => true,
            Exp::Same(w) => t.arity == w.arity && t.tuples.iter().any(|x| w.tuples.contains(x)),
            Exp::JoinRight(cols) => t.tuples.iter().any(|x| cols.contains(&x[0])),
            Exp::JoinLeft(cols) => t.tuples.iter().any(|x| cols.contains(&x[x.len() - 1])),
        }
    }

    /// Java `ExprChoice` resolution by type. Candidates not fitting the expected type are dropped; overloaded
    /// calls also need their (resolved) arguments to fit the parameter types. Several survivors stay a `Choice`.
    fn resolve(&mut self, e: &RExpr, exp: &Exp) -> Result<RExpr, AlloyError> {
        match e {
            RExpr::Block(items) if items.len() == 1 => self.resolve(&items[0], exp),
            RExpr::Choice(cands) => {
                let mut keep = Vec::new();
                for c in cands {
                    let c = match c {
                        RExpr::Call(fid, args) => {
                            let params = self.model.funcs[*fid as usize].params.clone();
                            if params.len() != args.len() {
                                continue;
                            }
                            let mut new_args = Vec::new();
                            let mut ok = true;
                            for (a, (_, pb)) in args.iter().zip(&params) {
                                let e2 = match self.ty(pb) {
                                    Some(w) => Exp::Same(w),
                                    None => Exp::Any,
                                };
                                match self.resolve(a, &e2) {
                                    Ok(r) => {
                                        if Self::is_choice(&r) || self.compatible(&r, &e2) {
                                            new_args.push(r)
                                        } else {
                                            ok = false;
                                            break;
                                        }
                                    }
                                    Err(_) => {
                                        ok = false;
                                        break;
                                    }
                                }
                            }
                            if !ok {
                                continue;
                            }
                            RExpr::Call(*fid, new_args)
                        }
                        other_c => other_c.clone(),
                    };
                    if self.compatible(&c, exp) {
                        keep.push(c);
                    }
                }
                match keep.len() {
                    0 => Err(other("no overloaded candidate matches the expected type")),
                    1 => Ok(keep.remove(0)),
                    _ => Ok(RExpr::Choice(keep)),
                }
            }
            RExpr::Bin(op @ (BinOp::Plus | BinOp::Intersect | BinOp::Override), a, b) if Self::is_choice(e) => {
                let a2 = self.resolve(a, exp)?;
                let b2 = self.resolve(b, exp)?;
                let (a2, b2) = self.resolve_pair(&a2, &b2)?;
                Ok(RExpr::Bin(*op, Box::new(a2), Box::new(b2)))
            }
            RExpr::Bin(BinOp::Minus, a, b) if Self::is_choice(e) => {
                let a2 = self.resolve(a, exp)?;
                let b2 = self.resolve_pair(&a2, b)?.1;
                Ok(RExpr::Bin(BinOp::Minus, Box::new(a2), Box::new(b2)))
            }
            RExpr::Un(UnOp::Transpose, x) if Self::is_choice(e) => {
                let flipped = match exp {
                    Exp::Any => Exp::Any,
                    Exp::Same(w) => {
                        Exp::Same(TupleSet::from_tuples(w.arity, w.tuples.iter().map(|t| t.iter().rev().copied().collect::<Vec<_>>())))
                    }
                    Exp::JoinRight(c) => Exp::JoinLeft(c.clone()),
                    Exp::JoinLeft(c) => Exp::JoinRight(c.clone()),
                };
                Ok(RExpr::Un(UnOp::Transpose, Box::new(self.resolve(x, &flipped)?)))
            }
            RExpr::Un(op @ (UnOp::Closure | UnOp::ReflClosure | UnOp::Set), x) if Self::is_choice(e) => {
                let exp2 = match exp {
                    Exp::Any => Exp::Any,
                    Exp::Same(w) => Exp::Same(w.clone()),
                    Exp::JoinRight(c) => Exp::JoinRight(c.clone()),
                    Exp::JoinLeft(c) => Exp::JoinLeft(c.clone()),
                };
                Ok(RExpr::Un(*op, Box::new(self.resolve(x, &exp2)?)))
            }
            _ => Ok(e.clone()),
        }
    }

    /// Does `e` contain an unresolved overload at a position `resolve` can reach?
    fn is_choice(e: &RExpr) -> bool {
        match e {
            RExpr::Choice(c) => c.len() > 1,
            RExpr::Block(items) if items.len() == 1 => Self::is_choice(&items[0]),
            RExpr::Bin(BinOp::Plus | BinOp::Minus | BinOp::Intersect | BinOp::Override, a, b) => {
                Self::is_choice(a) || Self::is_choice(b)
            }
            RExpr::Un(UnOp::Transpose | UnOp::Closure | UnOp::ReflClosure | UnOp::Set, x) => Self::is_choice(x),
            _ => false,
        }
    }

    /// Resolves the overloaded operands of a binary operator against each other (same arity/overlapping types).
    fn resolve_pair(&mut self, a: &RExpr, b: &RExpr) -> Result<(RExpr, RExpr), AlloyError> {
        let (mut a, mut b) = (a.clone(), b.clone());
        if Self::is_choice(&a) {
            let exp = if Self::is_choice(&b) { None } else { self.ty(&b) };
            a = self.resolve(&a, &exp.map_or(Exp::Any, Exp::Same))?;
        }
        if Self::is_choice(&b) {
            let exp = self.ty(&a);
            b = self.resolve(&b, &exp.map_or(Exp::Any, Exp::Same))?;
        }
        if Self::is_choice(&a) && !Self::is_choice(&b) {
            let exp = self.ty(&b);
            a = self.resolve(&a, &exp.map_or(Exp::Any, Exp::Same))?;
        }
        Ok((a, b))
    }

    /// Overloads of `a <: r` (domain = true: `a` against the first column of `r`) and `r :> b`.
    fn resolve_restrict(&mut self, a: &RExpr, b: &RExpr, domain: bool) -> Result<(RExpr, RExpr), AlloyError> {
        let (mut a, mut b) = (a.clone(), b.clone());
        if domain {
            if Self::is_choice(&b) {
                let exp = self.ty(&a).map(|t| Exp::JoinRight(t.tuples.iter().map(|x| x[0]).collect()));
                b = self.resolve(&b, &exp.unwrap_or(Exp::Any))?;
            }
        } else if Self::is_choice(&a) {
            let exp = self.ty(&b).map(|t| Exp::JoinLeft(t.tuples.iter().map(|x| x[0]).collect()));
            a = self.resolve(&a, &exp.unwrap_or(Exp::Any))?;
        }
        Ok((a, b))
    }

    /// Resolves the operands of a join `a.b`: last column of `a` against first column of `b`.
    fn resolve_join(&mut self, a: &RExpr, b: &RExpr) -> Result<(RExpr, RExpr), AlloyError> {
        let (mut a, mut b) = (a.clone(), b.clone());
        if Self::is_choice(&a) && !Self::is_choice(&b) {
            let exp = self.ty(&b).map(|t| Exp::JoinLeft(t.tuples.iter().map(|x| x[0]).collect()));
            a = self.resolve(&a, &exp.unwrap_or(Exp::Any))?;
        }
        if Self::is_choice(&b) {
            let exp = self.ty(&a).map(|t| Exp::JoinRight(t.tuples.iter().map(|x| x[x.len() - 1]).collect()));
            b = self.resolve(&b, &exp.unwrap_or(Exp::Any))?;
        }
        if Self::is_choice(&a) {
            let exp = self.ty(&b).map(|t| Exp::JoinLeft(t.tuples.iter().map(|x| x[0]).collect()));
            a = self.resolve(&a, &exp.unwrap_or(Exp::Any))?;
        }
        Ok((a, b))
    }

    /// `univ^k` for the k-ary complement used by domain/range restriction.
    fn univ_pow(&self, k: usize) -> Expr {
        let mut e = Expr::Const(KConst::Univ);
        for _ in 1..k {
            e = Expr::product(e, Expr::Const(KConst::Univ));
        }
        e
    }

    /// Relational expression of an Alloy expression.
    fn expr(&mut self, e: &RExpr) -> Result<Expr, AlloyError> {
        Ok(match e {
            RExpr::Sig(s) => self.sig_expr(*s)?,
            RExpr::Field(f) => self.field_expr(*f)?,
            RExpr::Local(l) => self
                .locals
                .get(l)
                .cloned()
                .ok_or_else(|| other(format!("unbound local {l}")))?,
            RExpr::Const(Const::Iden) => Expr::Const(KConst::Iden),
            RExpr::Const(c @ (Const::IntMin | Const::IntMax)) => Expr::IntToExpr(Box::new(self.int_of(&RExpr::Const(*c))?)),
            RExpr::Const(Const::IntNext) => self.int_next()?,
            RExpr::Const(other_c) => {
                return Err(unsupported(format!("constant {other_c:?} (temporal)")))
            }
            e @ (RExpr::Num(_) | RExpr::Un(UnOp::Card | UnOp::IntCast | UnOp::Neg, _)) => {
                Expr::IntToExpr(Box::new(self.int_of(e)?))
            }
            RExpr::Bin(BinOp::IntPlus | BinOp::IntMinus | BinOp::Mul, _, _) => {
                Expr::IntToExpr(Box::new(self.int_of(e)?))
            }
            RExpr::Un(UnOp::Set, x) => self.expr(x)?,
            RExpr::Un(UnOp::Transpose, x) => Expr::Transpose(Box::new(self.expr(x)?)),
            RExpr::Un(UnOp::Closure, x) => Expr::Closure(Box::new(self.expr(x)?)),
            RExpr::Un(UnOp::ReflClosure, x) => Expr::ReflexiveClosure(Box::new(self.expr(x)?)),
            RExpr::Un(op, _) => return Err(unsupported(format!("unary operator {op:?} in expression position"))),
            RExpr::Bin(BinOp::Join, a, b) => {
                let (a, b) = self.resolve_join(a, b)?;
                Expr::join(self.expr(&a)?, self.expr(&b)?)
            }
            RExpr::Bin(BinOp::Plus, a, b) => {
                let (a, b) = self.resolve_pair(a, b)?;
                Expr::union(self.expr(&a)?, self.expr(&b)?)
            }
            RExpr::Bin(BinOp::Minus, a, b) => {
                let (a, b) = self.resolve_pair(a, b)?;
                Expr::Difference(Box::new(self.expr(&a)?), Box::new(self.expr(&b)?))
            }
            RExpr::Bin(BinOp::Intersect, a, b) => {
                let (a, b) = self.resolve_pair(a, b)?;
                Expr::Intersection(Box::new(self.expr(&a)?), Box::new(self.expr(&b)?))
            }
            RExpr::Bin(BinOp::Override, a, b) => {
                let (a, b) = self.resolve_pair(a, b)?;
                Expr::Override(Box::new(self.expr(&a)?), Box::new(self.expr(&b)?))
            }
            RExpr::Bin(BinOp::Arrow(_, _), a, b) => {
                let (a, b) = self.resolve_pair(a, b)?;
                Expr::product(self.expr(&a)?, self.expr(&b)?)
            }
            RExpr::Bin(BinOp::DomainRestrict, a, b) => {
                // a <: r = (a -> univ^(k)) & r, k = arity(r) - 1
                let (a, b) = self.resolve_restrict(a, b, true)?;
                let (a, r) = (self.expr(&a)?, self.expr(&b)?);
                let k = self.arity(&r)? - 1;
                Expr::Intersection(Box::new(Expr::product(a, self.univ_pow(k))), Box::new(r))
            }
            RExpr::Bin(BinOp::RangeRestrict, r, b) => {
                // r :> b = (univ^(k) -> b) & r, k = arity(r) - 1
                let (r, b) = self.resolve_restrict(r, b, false)?;
                let (r, b) = (self.expr(&r)?, self.expr(&b)?);
                let k = self.arity(&r)? - 1;
                Expr::Intersection(Box::new(Expr::product(self.univ_pow(k), b)), Box::new(r))
            }
            RExpr::Bin(op, _, _) => return Err(unsupported(format!("binary operator {op:?} in expression position"))),
            RExpr::Compr(decls, body) => {
                let (kdecls, disj, guards) = self.decls(decls)?;
                let f = self.formula(body)?;
                let f = with_disjointness(f, &disj, &guards, false);
                Expr::Comprehension(kdecls, Box::new(f))
            }
            RExpr::Ite(c, a, b) => {
                let c = self.formula(c)?;
                Expr::IfThenElse(Box::new(c), Box::new(self.expr(a)?), Box::new(self.expr(b)?))
            }
            RExpr::Let(binds, body) => {
                let saved = self.bind_lets(binds)?;
                let r = self.expr(body);
                self.restore(saved);
                r?
            }
            RExpr::Call(fid, args) => {
                let f = &self.model.funcs[*fid as usize];
                if f.is_pred {
                    return Err(unsupported("predicate used as an expression"));
                }
                let body = f.body.clone();
                let params = f.params.clone();
                self.inline(&params, args, |tr| tr.expr(&body))?
            }
            RExpr::Block(items) if items.len() == 1 => self.expr(&items[0])?,
            RExpr::Choice(cands) if cands.len() == 1 => self.expr(&cands[0])?,
            RExpr::Choice(_) => {
                let r = self.resolve(e, &Exp::Any)?;
                if Self::is_choice(&r) {
                    let names: Vec<String> = match &r {
                        RExpr::Choice(cs) => cs
                            .iter()
                            .map(|c| match c {
                                RExpr::Call(f, _) => self.model.funcs[*f as usize].label.clone(),
                                RExpr::Field(f) => self.model.fields[*f as usize].label.clone(),
                                RExpr::Sig(s) => self.model.sigs[*s as usize].label.clone(),
                                other_c => format!("{:.30}", format!("{other_c:?}")),
                            })
                            .collect(),
                        _ => Vec::new(),
                    };
                    return Err(unsupported(format!("overloaded name still ambiguous after type resolution (M3.4): {}", names.join(" | "))));
                }
                self.expr(&r)?
            }
            RExpr::Quant(..) | RExpr::Block(_) | RExpr::Disj(_) | RExpr::TotalOrder(_) => {
                return Err(other("formula used where an expression is expected"))
            }
        })
    }

    /// Integer expression of a numeric Alloy expression (`Alloy.cup` implicit casts: a set of integer atoms
    /// is summed, a number is a constant).
    fn int_of(&mut self, e: &RExpr) -> Result<IntExpr, AlloyError> {
        Ok(match e {
            RExpr::Num(n) => IntExpr::Const(*n as i64),
            RExpr::Const(Const::IntMin) => IntExpr::Const(self.int_min()),
            RExpr::Const(Const::IntMax) => IntExpr::Const(-self.int_min() - 1),
            RExpr::Un(UnOp::Card, x) => IntExpr::Card(Box::new(self.expr(x)?)),
            RExpr::Un(UnOp::IntCast, x) if is_numeric(x) => self.int_of(x)?,
            RExpr::Un(UnOp::IntCast, x) => IntExpr::Sum(Box::new(self.expr(x)?)),
            RExpr::Un(UnOp::Neg, x) => IntExpr::Neg(Box::new(self.int_of(x)?)),
            RExpr::Block(items) if items.len() == 1 => self.int_of(&items[0])?,
            RExpr::Bin(BinOp::IntPlus, a, b) => IntExpr::Add(Box::new(self.int_of(a)?), Box::new(self.int_of(b)?)),
            RExpr::Bin(BinOp::IntMinus, a, b) => IntExpr::Sub(Box::new(self.int_of(a)?), Box::new(self.int_of(b)?)),
            RExpr::Bin(BinOp::Mul, a, b) => IntExpr::Mul(Box::new(self.int_of(a)?), Box::new(self.int_of(b)?)),
            RExpr::Bin(op @ (BinOp::Div | BinOp::Rem), _, _) => {
                return Err(unsupported(format!("integer {op:?} (M5.5)")))
            }
            other => IntExpr::Sum(Box::new(self.expr(other)?)),
        })
    }

    /// Minimum integer of the bitwidth (`-2^(w-1)`); 0 when there are no integers.
    fn int_min(&self) -> i64 {
        self.bounds.int_min
    }

    /// `Int`'s successor relation `next = {(i, i+1)}` over the integer atoms (Java `Const.IntNext`).
    fn int_next(&self) -> Result<Expr, AlloyError> {
        let n = if self.bounds.bitwidth == 0 { 0 } else { 1u32 << self.bounds.bitwidth };
        let start = self.bounds.int_start;
        let ts = TupleSet::from_tuples(2, (0..n.saturating_sub(1)).map(|k| vec![start + k, start + k + 1]));
        Ok(Expr::Literal(ts))
    }

    /// Formula of an Alloy formula expression.
    fn formula(&mut self, e: &RExpr) -> Result<Formula, AlloyError> {
        Ok(match e {
            RExpr::Block(items) => Formula::And(items.iter().map(|x| self.formula(x)).collect::<Result<_, _>>()?),
            RExpr::Bin(BinOp::And, a, b) => Formula::And(vec![self.formula(a)?, self.formula(b)?]),
            RExpr::Bin(BinOp::Or, a, b) => Formula::Or(vec![self.formula(a)?, self.formula(b)?]),
            RExpr::Bin(BinOp::Implies, a, b) => {
                self.pol = !self.pol;
                let a = self.formula(a);
                self.pol = !self.pol;
                Formula::Implies(Box::new(a?), Box::new(self.formula(b)?))
            }
            RExpr::Bin(BinOp::Iff, a, b) => Formula::Iff(Box::new(self.formula(a)?), Box::new(self.formula(b)?)),
            // Java `visit(ExprBinary) EQUALS`: integer equality only when both sides are integer-typed, else set equality.
            RExpr::Bin(BinOp::Equals, a, b) if is_numeric(a) && is_numeric(b) => {
                Formula::IntCompare(IntCmp::Eq, self.int_of(a)?, self.int_of(b)?)
            }
            RExpr::Bin(BinOp::Equals, a, b) => {
                let (a, b) = self.resolve_pair(a, b)?;
                Formula::Equal(self.expr(&a)?, self.expr(&b)?)
            }
            RExpr::Bin(BinOp::In, a, b) => {
                let (a, b) = self.resolve_pair(a, b)?;
                let lhs = self.expr(&a)?;
                self.in_formula(lhs, &b)?
            }
            RExpr::Bin(BinOp::Lt, a, b) => Formula::IntCompare(IntCmp::Lt, self.int_of(a)?, self.int_of(b)?),
            RExpr::Bin(BinOp::Le, a, b) => Formula::IntCompare(IntCmp::Le, self.int_of(a)?, self.int_of(b)?),
            RExpr::Bin(BinOp::Gt, a, b) => Formula::IntCompare(IntCmp::Lt, self.int_of(b)?, self.int_of(a)?),
            RExpr::Bin(BinOp::Ge, a, b) => Formula::IntCompare(IntCmp::Le, self.int_of(b)?, self.int_of(a)?),
            RExpr::Un(UnOp::Not, x) => {
                self.pol = !self.pol;
                let r = self.formula(x);
                self.pol = !self.pol;
                Formula::Not(Box::new(r?))
            }
            RExpr::Un(UnOp::No, x) => Formula::Multiplicity(Multiplicity::No, self.expr(x)?),
            RExpr::Un(UnOp::Some, x) => Formula::Multiplicity(Multiplicity::Some, self.expr(x)?),
            RExpr::Un(UnOp::One, x) => Formula::Multiplicity(Multiplicity::One, self.expr(x)?),
            RExpr::Un(UnOp::Lone, x) => Formula::Multiplicity(Multiplicity::Lone, self.expr(x)?),
            RExpr::Quant(q, decls, body) => self.quantified(*q, decls, body)?,
            RExpr::Ite(c, a, b) => {
                let (c, a, b) = (self.formula(c)?, self.formula(a)?, self.formula(b)?);
                Formula::Or(vec![
                    Formula::And(vec![c.clone(), a]),
                    Formula::And(vec![Formula::Not(Box::new(c)), b]),
                ])
            }
            RExpr::Let(binds, body) => {
                let saved = self.bind_lets(binds)?;
                let r = self.formula(body);
                self.restore(saved);
                r?
            }
            RExpr::Call(fid, args) => {
                let f = &self.model.funcs[*fid as usize];
                if !f.is_pred {
                    return Err(other("function used as a formula"));
                }
                let body = f.body.clone();
                let params = f.params.clone();
                self.inline(&params, args, |tr| tr.formula(&body))?
            }
            RExpr::Disj(args) => {
                let mut ks = Vec::new();
                for a in args {
                    ks.push(self.expr(a)?);
                }
                let mut parts = Vec::new();
                for i in 0..ks.len() {
                    for j in i + 1..ks.len() {
                        let inter = Expr::Intersection(Box::new(ks[i].clone()), Box::new(ks[j].clone()));
                        parts.push(Formula::Multiplicity(Multiplicity::No, inter));
                    }
                }
                Formula::And(parts)
            }
            RExpr::TotalOrder(args) => {
                // Java `ExprList.Op.TOTALORDER` (general form): `first` is in `elem`, has no predecessor, and
                // every element is `first` or has one predecessor, is `last` or has one successor, and no
                // element is reachable from itself.
                if args.len() != 3 {
                    return Err(other("pred/totalOrder takes exactly three arguments"));
                }
                if total_order_key(args).map_or(false, |k| self.pinned.contains(&k)) {
                    return Ok(Formula::True);
                }
                let elem = self.expr(&args[0])?;
                let first = self.expr(&args[1])?;
                let next = self.expr(&args[2])?;
                let f1 = Formula::Subset(
                    elem.clone(),
                    Expr::join(first.clone(), Expr::ReflexiveClosure(Box::new(next.clone()))),
                );
                let f2 = Formula::Multiplicity(Multiplicity::No, Expr::join(next.clone(), first.clone()));
                let e = self.fresh();
                let ev = Expr::Var(e);
                let f3 = Formula::Or(vec![
                    Formula::Equal(ev.clone(), first.clone()),
                    Formula::Multiplicity(Multiplicity::One, Expr::join(next.clone(), ev.clone())),
                ]);
                let last = Expr::Difference(
                    Box::new(elem.clone()),
                    Box::new(Expr::join(next.clone(), elem.clone())),
                );
                let f4 = Formula::Or(vec![
                    Formula::Equal(ev.clone(), last),
                    Formula::Multiplicity(Multiplicity::One, Expr::join(ev.clone(), next.clone())),
                ]);
                let f5 = Formula::Not(Box::new(Formula::Subset(
                    ev.clone(),
                    Expr::join(ev.clone(), Expr::Closure(Box::new(next.clone()))),
                )));
                let all = Formula::Quantified(
                    Quantifier::All,
                    vec![Decl { var: e, domain: elem.clone(), disjoint: false, set: false }],
                    Box::new(Formula::And(vec![f3, f4, f5])),
                );
                // The native predicate (used by Java for relation arguments) also requires `first` to be one atom of `elem`.
                let f0 = Formula::And(vec![
                    Formula::Multiplicity(Multiplicity::One, first.clone()),
                    Formula::Subset(first.clone(), elem.clone()),
                ]);
                // The domain and range of `next` lie inside `elem` (util/ordering's documented requirement).
                let f6 = Formula::Subset(next.clone(), Expr::product(elem.clone(), elem.clone()));
                Formula::And(vec![all, f1, f2, f0, f6])
            }
            RExpr::Choice(cands) if cands.len() == 1 => self.formula(&cands[0])?,
            RExpr::Choice(_) => return Err(unsupported("overloaded name (ExprChoice, M3.4)")),
            other_e => {
                let dbg = format!("{other_e:?} :: {}", self.model.funcs.iter().enumerate().filter(|(i, _)| [35usize, 36, 138].contains(i)).map(|(i, f)| format!("{i}={} params={}", f.label, f.params.len())).collect::<Vec<_>>().join(", "));
                return Err(other(format!("expression used as a formula: {} {}", kind_name(other_e), &dbg[..dbg.len().min(400)])))
            }
        })
    }

    fn quantified(&mut self, q: Quant, decls: &[RDecl], body: &RExpr) -> Result<Formula, AlloyError> {
        // Effective quantifier after polarity: `all` in positive position (or `some` in negative) is universal.
        let eff_universal = (q == Quant::All) == self.pol;
        let has_set = decls.iter().any(|d| matches!(d.bound, RExpr::Un(UnOp::Set, _)) || self.ty(&d.bound).map_or(false, |t| t.arity > 1));
        if has_set && (eff_universal || self.under_universal) {
            return Err(AlloyError::new(
                ErrorKind::Type,
                None,
                format!("Analysis cannot be performed since it requires higher-order quantification that could not be skolemized. {:.200}", format!("{decls:?}")),
            ));
        }
        let saved_under = self.under_universal;
        self.under_universal |= eff_universal;
        let r = self.quantified_body(q, decls, body);
        self.under_universal = saved_under;
        r
    }

    fn quantified_body(&mut self, q: Quant, decls: &[RDecl], body: &RExpr) -> Result<Formula, AlloyError> {
        let (kdecls, disj, guards) = self.decls(decls)?;
        let b = self.formula(body)?;
        let b = with_disjointness(b, &disj, &guards, q == Quant::All);
        Ok(match q {
            Quant::All => Formula::Quantified(Quantifier::All, kdecls, Box::new(b)),
            Quant::Some => Formula::Quantified(Quantifier::Some, kdecls, Box::new(b)),
            Quant::No => Formula::Not(Box::new(Formula::Quantified(Quantifier::Some, kdecls, Box::new(b)))),
            Quant::Lone | Quant::One => {
                // "at most one": for all x,y in dom: f(x) & f(y) => x = y. Needs one copy per variable.
                if decls.iter().map(|d| d.vars.len()).sum::<usize>() != 1 {
                    return Err(unsupported("lone/one quantifier over several variables (M5.4)"));
                }
                let (kdecls2, _, _) = self.decls(decls)?;
                let x = kdecls[0].var;
                let y = kdecls2[0].var;
                let bx = b.clone();
                let by = self.formula(body)?;
                let by = with_disjointness(by, &disj, &guards, false);
                let eq = Formula::Equal(Expr::Var(x), Expr::Var(y));
                let uniq = Formula::Quantified(
                    Quantifier::All,
                    vec![kdecls[0].clone(), kdecls2[0].clone()],
                    Box::new(Formula::Implies(
                        Box::new(Formula::And(vec![bx, by])),
                        Box::new(eq),
                    )),
                );
                if q == Quant::Lone {
                    uniq
                } else {
                    Formula::And(vec![
                        Formula::Quantified(Quantifier::Some, kdecls, Box::new(b)),
                        uniq,
                    ])
                }
            }
            Quant::Sum => return Err(unsupported("sum quantifier (integers)")),
        })
    }

    /// `lhs in rhs` where `rhs` may carry arrow multiplicities (`L m1 -> m2 R`) or a multiplicity keyword
    /// (Java `TranslateAlloyToKodkod.isIn`).
    fn in_formula(&mut self, lhs: Expr, rhs: &RExpr) -> Result<Formula, AlloyError> {
        match rhs {
            RExpr::Block(items) if items.len() == 1 => self.in_formula(lhs, &items[0]),
            RExpr::Bin(BinOp::Arrow(ml, mr), l, r) if *ml != Mult::Set || *mr != Mult::Set || has_arrow_mult(l) || has_arrow_mult(r) => {
                let (l, r) = self.resolve_pair(l, r)?;
                let (lx, rx) = (self.expr(&l)?, self.expr(&r)?);
                let mut out = vec![Formula::Subset(lhs.clone(), Expr::product(lx.clone(), rx.clone()))];
                // m2: every left tuple has m2 images.
                if mr_is_mult(*mr) || has_arrow_mult(&r) {
                    let x = self.fresh();
                    let a = self.arity(&lx)?;
                    self.local_arity.insert(x, a);
                    let img = Expr::join(Expr::Var(x), lhs.clone());
                    let body = if has_arrow_mult(&r) && !mr_is_mult(*mr) {
                        self.in_formula(img, &r)?
                    } else {
                        let m = mult_of(Some(*mr)).unwrap();
                        let mut parts = vec![Formula::Multiplicity(m, img.clone())];
                        if has_arrow_mult(&r) {
                            parts.push(self.in_formula(img, &r)?);
                        }
                        Formula::And(parts)
                    };
                    out.push(Formula::Quantified(
                        Quantifier::All,
                        vec![Decl { var: x, domain: lx.clone(), disjoint: false, set: false }],
                        Box::new(body),
                    ));
                }
                if mr_is_mult(*ml) || has_arrow_mult(&l) {
                    let y = self.fresh();
                    let a = self.arity(&rx)?;
                    self.local_arity.insert(y, a);
                    let img = Expr::join(lhs.clone(), Expr::Var(y));
                    let body = if has_arrow_mult(&l) && !mr_is_mult(*ml) {
                        self.in_formula(img, &l)?
                    } else {
                        let m = mult_of(Some(*ml)).unwrap();
                        let mut parts = vec![Formula::Multiplicity(m, img.clone())];
                        if has_arrow_mult(&l) {
                            parts.push(self.in_formula(img, &l)?);
                        }
                        Formula::And(parts)
                    };
                    out.push(Formula::Quantified(
                        Quantifier::All,
                        vec![Decl { var: y, domain: rx.clone(), disjoint: false, set: false }],
                        Box::new(body),
                    ));
                }
                Ok(Formula::And(out))
            }
            RExpr::Un(op @ (UnOp::One | UnOp::Lone | UnOp::Some), x) => {
                let m = match op {
                    UnOp::One => Multiplicity::One,
                    UnOp::Lone => Multiplicity::Lone,
                    _ => Multiplicity::Some,
                };
                let inner = self.in_formula(lhs.clone(), x)?;
                Ok(Formula::And(vec![inner, Formula::Multiplicity(m, lhs)]))
            }
            RExpr::Un(UnOp::Set, x) => self.in_formula(lhs, x),
            other_r => Ok(Formula::Subset(lhs, self.expr(other_r)?)),
        }
    }

    /// Declares the variables of `decls` (one kodkod variable per Alloy variable) and returns the
    /// kodkod declarations plus the `disj` groups as lists of variable ids.
    fn decls(&mut self, decls: &[RDecl]) -> Result<(Vec<Decl>, Vec<Vec<u32>>, Vec<Formula>), AlloyError> {
        let mut out = Vec::new();
        let mut disj = Vec::new();
        let mut guards = Vec::new();
        for d in decls {
            // `x: set e` ranges over subsets, `x: one e` (the default) over the tuples of `e`; a bound of
            // arity > 1 (`x: A -> one B`) is a relation-valued variable constrained by its multiplicities.
            let (bound, mut is_set) = match &d.bound {
                RExpr::Un(UnOp::Set, x) => (&**x, true),
                RExpr::Un(UnOp::One, x) => (&**x, false),
                RExpr::Un(UnOp::Lone | UnOp::Some, _) => {
                    return Err(unsupported("lone/some declaration multiplicities (M5.4)"))
                }
                other => (other, false),
            };
            let domain = self.expr(bound)?;
            let a = self.arity(&domain)?;
            let higher_arity = a > 1;
            if higher_arity {
                is_set = true;
            }
            for &l in &d.vars {
                self.local_bound.insert(l, bound.clone());
            }
            let mut group = Vec::new();
            for &l in &d.vars {
                let v = self.fresh();
                self.local_arity.insert(v, a);
                self.locals.insert(l, Expr::Var(v));
                if higher_arity && has_arrow_mult(bound) {
                    guards.push(self.in_formula(Expr::Var(v), bound)?);
                }
                out.push(Decl {
                    var: v,
                    domain: domain.clone(),
                    disjoint: d.disjoint,
                    set: is_set,
                });
                group.push(v);
            }
            if d.disjoint && group.len() > 1 {
                disj.push(group);
            }
        }
        Ok((out, disj, guards))
    }

    fn bind_lets(&mut self, binds: &[(LocalId, RExpr)]) -> Result<Vec<(LocalId, Option<Expr>)>, AlloyError> {
        let mut saved = Vec::new();
        for (l, e) in binds {
            let v = self.expr(e)?;
            self.local_bound.insert(*l, e.clone());
            saved.push((*l, self.locals.insert(*l, v)));
        }
        Ok(saved)
    }

    fn restore(&mut self, saved: Vec<(LocalId, Option<Expr>)>) {
        for (l, old) in saved.into_iter().rev() {
            match old {
                Some(v) => {
                    self.locals.insert(l, v);
                }
                None => {
                    self.locals.remove(&l);
                }
            }
        }
    }

    /// Inlines a predicate/function call: parameters are bound to the argument expressions (evaluated
    /// in the caller's scope first), the body is translated, and the old bindings are restored.
    fn inline<T>(
        &mut self,
        params: &[(LocalId, RExpr)],
        args: &[RExpr],
        body: impl FnOnce(&mut Self) -> Result<T, AlloyError>,
    ) -> Result<T, AlloyError> {
        if params.len() != args.len() {
            return Err(other(format!("call with {} arguments, but the callee takes {}", args.len(), params.len())));
        }
        if self.depth >= MAX_CALL_DEPTH {
            return Err(unsupported("recursive predicate/function (too deep to inline)"));
        }
        let mut vals = Vec::new();
        for (a, (_, pb)) in args.iter().zip(params) {
            let a = if Self::is_choice(a) {
                let exp = self.ty(pb).map_or(Exp::Any, Exp::Same);
                self.resolve(a, &exp)?
            } else {
                a.clone()
            };
            vals.push(self.expr(&a)?);
        }
        let mut saved = Vec::new();
        for ((l, b), v) in params.iter().zip(vals) {
            // Parameters keep their declared bound, so overloaded names used on them can be typed.
            self.local_bound.insert(*l, b.clone());
            saved.push((*l, self.locals.insert(*l, v)));
        }
        self.depth += 1;
        let r = body(self);
        self.depth -= 1;
        self.restore(saved);
        r
    }

    /// `all s: sig | ...` constraints of the sig hierarchy (Java `TranslateAlloyToKodkod.visit(Sig)`).
    fn sig_constraints(&mut self) -> Result<Vec<Formula>, AlloyError> {
        let mut out = std::mem::take(&mut self.sig_disjoint);
        let n = self.model.sigs.len();
        for i in 0..n {
            let sig = &self.model.sigs[i];
            if sig.kind != SigKind::User {
                continue;
            }
            let me = self.sig_expr(i as SigId)?;
            if !sig.subset_of.is_empty() {
                let mut targets = Vec::new();
                for &t in &sig.subset_of {
                    targets.push(self.sig_expr(t)?);
                }
                let rhs = targets.into_iter().reduce(Expr::union).unwrap();
                out.push(if sig.is_exact {
                    Formula::Equal(me.clone(), rhs)
                } else {
                    Formula::Subset(me.clone(), rhs)
                });
            }
            match sig.mult {
                Some(Mult::One) => out.push(Formula::Multiplicity(Multiplicity::One, me)),
                Some(Mult::Lone) => out.push(Formula::Multiplicity(Multiplicity::Lone, me)),
                Some(Mult::Some) => out.push(Formula::Multiplicity(Multiplicity::Some, me)),
                _ => {}
            }
        }
        Ok(out)
    }

    /// Field constraints: `f in owner -> decl`, declared multiplicities, and defined fields `f = e`.
    fn field_constraints(&mut self) -> Result<Vec<Formula>, AlloyError> {
        let mut out = Vec::new();
        for g in self.model.field_disjoint.clone() {
            for i in 0..g.len() {
                for j in i + 1..g.len() {
                    let inter = Expr::Intersection(Box::new(self.field_expr(g[i])?), Box::new(self.field_expr(g[j])?));
                    out.push(Formula::Multiplicity(Multiplicity::No, inter));
                }
            }
        }
        let nf = self.model.fields.len();
        for fi in 0..nf {
            let f = self.model.fields[fi].clone();
            let rel = self.field_expr(fi as FieldId)?;
            let owner = self.sig_expr(f.owner)?;
            if f.defined {
                let rhs = self.expr(&f.decl)?;
                out.push(Formula::Equal(rel.clone(), rhs));
                continue;
            }
            // `all this: owner | this.f in decl` (the multiplicity keyword or arrow multiplicities apply per `this`).
            let this = self.fresh();
            self.local_arity.insert(this, 1);
            self.locals.insert(f.this_local, Expr::Var(this));
            self.local_bound.insert(f.this_local, RExpr::Sig(f.owner));
            let lhs = Expr::join(Expr::Var(this), rel.clone());
            let decl = match f.mult {
                Some(m) => RExpr::Un(
                    match m {
                        Mult::One => UnOp::One,
                        Mult::Lone => UnOp::Lone,
                        Mult::Some => UnOp::Some,
                        Mult::Set => UnOp::Set,
                    },
                    Box::new(f.decl.clone()),
                ),
                None => {
                    // Java `Sig.addField`: no multiplicity symbol on a unary bound means `one`.
                    let unary = match self.expr(&f.decl) {
                        Ok(e) => self.arity(&e).map_or(false, |a| a == 1),
                        Err(_) => false,
                    };
                    if unary {
                        RExpr::Un(UnOp::One, Box::new(f.decl.clone()))
                    } else {
                        f.decl.clone()
                    }
                }
            };
            let body = self.in_formula(lhs, &decl);
            self.locals.remove(&f.this_local);
            self.local_bound.remove(&f.this_local);
            let body = body?;
            out.push(Formula::Subset(rel.clone(), Expr::product(owner.clone(), self.univ_pow(self.arity(&rel)? - 1))));
            out.push(Formula::Quantified(
                Quantifier::All,
                vec![Decl { var: this, domain: owner, disjoint: false, set: false }],
                Box::new(body),
            ));
        }
        Ok(out)
    }
}

fn mr_is_mult(m: Mult) -> bool {
    mult_of(Some(m)).is_some()
}

/// Is `e` an arrow with a multiplicity somewhere inside?
fn has_arrow_mult(e: &RExpr) -> bool {
    match e {
        RExpr::Bin(BinOp::Arrow(a, b), l, r) => *a != Mult::Set || *b != Mult::Set || has_arrow_mult(l) || has_arrow_mult(r),
        RExpr::Block(items) if items.len() == 1 => has_arrow_mult(&items[0]),
        _ => false,
    }
}

fn mult_of(m: Option<Mult>) -> Option<Multiplicity> {
    match m {
        Some(Mult::One) => Some(Multiplicity::One),
        Some(Mult::Lone) => Some(Multiplicity::Lone),
        Some(Mult::Some) => Some(Multiplicity::Some),
        _ => None,
    }
}

/// `disj` groups: every pair of variables in a group is distinct. For a body `b`, the constraint
/// is added as a guard, so both `all` (implication) and `some` (conjunction) read it correctly.
fn with_disjointness(b: Formula, groups: &[Vec<u32>], guards: &[Formula], universal: bool) -> Formula {
    let mut parts: Vec<Formula> = guards.to_vec();
    for g in groups {
        for i in 0..g.len() {
            for j in i + 1..g.len() {
                parts.push(Formula::Not(Box::new(Formula::Equal(Expr::Var(g[i]), Expr::Var(g[j])))));
            }
        }
    }
    if parts.is_empty() {
        b
    } else if universal {
        // all disj x, y | f  ==  all x, y | (x != y) => f
        Formula::Implies(Box::new(Formula::And(parts)), Box::new(b))
    } else {
        // some disj x, y | f  ==  some x, y | (x != y) and f
        parts.push(b);
        Formula::And(parts)
    }
}

fn kind_name(e: &RExpr) -> &'static str {
    match e {
        RExpr::Sig(_) => "sig",
        RExpr::Field(_) => "field",
        RExpr::Local(_) => "local",
        RExpr::Const(_) => "const",
        RExpr::Num(_) => "number",
        RExpr::Un(_, _) => "unary",
        RExpr::Bin(_, _, _) => "binary",
        RExpr::Quant(_, _, _) => "quantifier",
        RExpr::Compr(_, _) => "comprehension",
        RExpr::Ite(_, _, _) => "ite",
        RExpr::Let(_, _) => "let",
        RExpr::Call(_, _) => "call",
        RExpr::Block(_) => "block",
        RExpr::Disj(_) => "disj",
        RExpr::TotalOrder(_) => "totalOrder",
        RExpr::Choice(_) => "choice",
    }
}
