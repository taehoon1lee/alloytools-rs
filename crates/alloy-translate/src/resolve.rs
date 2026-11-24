//! Port of `edu.mit.csail.sdg.ast.ExprChoice.resolve` (type-directed overload resolution), shared by the fast
//! translator (`translate.rs`) and the exact pipeline (`exact/`). Types are atom-level upper bounds (`type_of`).
//! Candidates that do not fit the expected type are dropped; overloaded calls also need their (resolved) arguments
//! to fit the parameter types; several survivors stay a `Choice`. The expected type is propagated through joins
//! (Java resolves top-down: `ExprBinary.resolve` then `ExprChoice.resolve`).

use alloy_core::error::{AlloyError, ErrorKind};
use alloy_core::sema::{
    FieldId, LocalId, Model, RExpr, SigId, SigKind, SIG_INT, SIG_NONE, SIG_SEQINT, SIG_STRING,
    SIG_UNIV,
};
use alloy_core::syntax::{BinOp, Const, Quant, UnOp};
use std::collections::{BTreeSet, HashMap};

use crate::scope::Layout;

/// Atom-level upper bound tuple set for overload resolution (`ExprChoice.resolve`).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct TupleSet {
    pub arity: usize,
    pub tuples: BTreeSet<Vec<u32>>,
}

impl TupleSet {
    pub fn empty(arity: usize) -> Self {
        TupleSet {
            arity,
            tuples: BTreeSet::new(),
        }
    }

    pub fn from_tuples(arity: usize, tuples: impl IntoIterator<Item = Vec<u32>>) -> Self {
        let mut t = TupleSet::empty(arity);
        for x in tuples {
            debug_assert_eq!(x.len(), arity);
            t.tuples.insert(x);
        }
        t
    }

    pub fn union(&self, o: &TupleSet) -> TupleSet {
        TupleSet {
            arity: self.arity,
            tuples: self.tuples.union(&o.tuples).cloned().collect(),
        }
    }

    pub fn product(&self, o: &TupleSet) -> TupleSet {
        let mut out = BTreeSet::new();
        for a in &self.tuples {
            for b in &o.tuples {
                let mut t = a.clone();
                t.extend_from_slice(b);
                out.insert(t);
            }
        }
        TupleSet {
            arity: self.arity + o.arity,
            tuples: out,
        }
    }
}

fn unsupported(msg: impl Into<String>) -> AlloyError {
    AlloyError::unsupported(msg)
}

fn other(msg: impl Into<String>) -> AlloyError {
    AlloyError::new(ErrorKind::Other, None, msg)
}

fn unary(atoms: Vec<u32>) -> TupleSet {
    TupleSet::from_tuples(1, atoms.into_iter().map(|a| vec![a]))
}

/// Upper atoms of a sig, including subset sigs (`sig A in B + C` may take the atoms of B and C).
fn sig_upper(model: &Model, lay: &Layout, s: SigId, n_atoms: u32) -> Result<Vec<u32>, AlloyError> {
    let sig = &model.sigs[s as usize];
    if sig.kind == SigKind::Builtin {
        return Ok(match s {
            SIG_UNIV => (0..n_atoms)
                .filter(|a| *a < lay.time_range.0 || *a >= lay.time_range.1)
                .collect(),
            SIG_NONE => Vec::new(),
            SIG_INT => (lay.atoms.len() as u32..n_atoms).collect(),
            SIG_STRING => (lay.string_range.0..lay.string_range.1).collect(),
            SIG_SEQINT => (lay.atoms.len() as u32..n_atoms).collect(),
            _ => {
                return Err(unsupported(format!(
                    "builtin sig {} (strings/seq)",
                    sig.label
                )))
            }
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

/// Type (upper-bound tuples) of an Alloy expression in the current scope.
pub(crate) fn type_of(
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
        RExpr::Const(Const::Univ) => unary(
            (0..n_atoms)
                .filter(|a| *a < lay.time_range.0 || *a >= lay.time_range.1)
                .collect(),
        ),
        RExpr::Const(Const::None) => TupleSet::empty(1),
        RExpr::Un(UnOp::Set | UnOp::One | UnOp::Lone | UnOp::Some | UnOp::Prime, x) => t!(x),
        RExpr::Un(UnOp::Seq, x) => {
            unary(sig_upper(model, lay, SIG_SEQINT, n_atoms)?).product(&t!(x))
        }
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
            let has_plain = c
                .iter()
                .any(|x| !matches!(x, RExpr::Choice(v) if v.len() == 1));
            for x in c {
                if has_plain && matches!(x, RExpr::Choice(v) if v.len() == 1) {
                    continue;
                }
                let t = t!(x);
                acc = Some(match acc {
                    Some(a) if a.arity == t.arity => a.union(&t),
                    Some(a) => a,
                    None => t,
                });
            }
            acc.ok_or_else(|| other("empty choice"))?
        }
        RExpr::Str(text) => {
            let name = format!("\"{text}\"");
            match lay.atoms.iter().position(|x| *x == name) {
                Some(a) => unary(vec![a as u32]),
                None => TupleSet::empty(1),
            }
        }
        RExpr::Const(Const::Iden) => {
            let all = unary((0..n_atoms).collect());
            TupleSet::from_tuples(2, all.tuples.iter().map(|t| vec![t[0], t[0]]))
        }
        RExpr::Const(Const::IntNext)
        | RExpr::Const(Const::IntMin)
        | RExpr::Const(Const::IntMax) => {
            let ints = unary(sig_upper(model, lay, SIG_INT, n_atoms)?);
            if matches!(e, RExpr::Const(Const::IntNext)) {
                ints.product(&ints)
            } else {
                ints
            }
        }
        RExpr::Num(_)
        | RExpr::Quant(Quant::Sum, _, _)
        | RExpr::Un(UnOp::Card | UnOp::IntCast | UnOp::SigInt | UnOp::Neg, _)
        | RExpr::Bin(
            BinOp::IntPlus | BinOp::IntMinus | BinOp::Mul | BinOp::Div | BinOp::Rem,
            _,
            _,
        ) => unary(sig_upper(model, lay, SIG_INT, n_atoms)?),
        RExpr::Un(UnOp::Closure | UnOp::ReflClosure, x) => {
            let a = t!(x);
            let mut out = TupleSet::empty(2);
            let firsts: BTreeSet<u32> = a.tuples.iter().map(|t| t[0]).collect();
            let lasts: BTreeSet<u32> = a.tuples.iter().map(|t| t[t.len() - 1]).collect();
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
            TupleSet::from_tuples(
                a.arity,
                a.tuples
                    .iter()
                    .map(|t| t.iter().rev().copied().collect::<Vec<_>>()),
            )
        }
        other_e => {
            return Err(unsupported(format!(
                "declaration type that is not a sig expression: {:.80}",
                format!("{other_e:?}")
            )))
        }
    })
}

/// Expected type of an overloaded operand.
pub(crate) enum Exp {
    Any,
    /// Same arity and at least one common tuple.
    Same(TupleSet),
    /// Candidate's first column must hit these atoms (it is the right operand of a join).
    JoinRight(std::collections::BTreeSet<u32>),
    /// Candidate's last column must hit these atoms (it is the left operand of a join).
    JoinLeft(std::collections::BTreeSet<u32>),
}

impl Exp {
    fn same_or_any(t: Option<TupleSet>) -> Exp {
        t.map_or(Exp::Any, Exp::Same)
    }
}

fn err(msg: impl Into<String>) -> AlloyError {
    AlloyError::new(ErrorKind::Other, None, msg.into())
}

/// A one-element `Choice` marks a penalized candidate (Java `ExprChoice` weight); this strips the marks.
fn unmark(e: &RExpr) -> RExpr {
    match e {
        RExpr::Choice(v) if v.len() == 1 => unmark(&v[0]),
        RExpr::Bin(op, a, b) => RExpr::Bin(*op, Box::new(unmark(a)), Box::new(unmark(b))),
        RExpr::Un(op, x) => RExpr::Un(*op, Box::new(unmark(x))),
        other => other.clone(),
    }
}

/// Does `e` contain an unresolved overload at a position `resolve` can reach?
pub(crate) fn is_choice(e: &RExpr) -> bool {
    match e {
        RExpr::Choice(c) => c.len() > 1,
        RExpr::Block(items) if items.len() == 1 => is_choice(&items[0]),
        RExpr::Bin(
            BinOp::Plus | BinOp::Minus | BinOp::Intersect | BinOp::Override | BinOp::Join,
            a,
            b,
        ) => is_choice(a) || is_choice(b),
        RExpr::Un(UnOp::Transpose | UnOp::Closure | UnOp::ReflClosure | UnOp::Set, x) => {
            is_choice(x)
        }
        _ => false,
    }
}

/// The alternatives of the first reachable overload in `e`, each substituted into `e`.
fn alternatives(e: &RExpr) -> Option<Vec<RExpr>> {
    match e {
        RExpr::Choice(c) if c.len() > 1 => Some(c.clone()),
        RExpr::Block(items) if items.len() == 1 => alternatives(&items[0]),
        RExpr::Bin(
            op @ (BinOp::Plus | BinOp::Minus | BinOp::Intersect | BinOp::Override | BinOp::Join),
            a,
            b,
        ) => {
            if is_choice(a) {
                Some(
                    alternatives(a)?
                        .into_iter()
                        .map(|x| RExpr::Bin(*op, Box::new(x), b.clone()))
                        .collect(),
                )
            } else if is_choice(b) {
                Some(
                    alternatives(b)?
                        .into_iter()
                        .map(|x| RExpr::Bin(*op, a.clone(), Box::new(x)))
                        .collect(),
                )
            } else {
                None
            }
        }
        RExpr::Un(op @ (UnOp::Transpose | UnOp::Closure | UnOp::ReflClosure | UnOp::Set), x) => {
            Some(
                alternatives(x)?
                    .into_iter()
                    .map(|y| RExpr::Un(*op, Box::new(y)))
                    .collect(),
            )
        }
        _ => None,
    }
}

pub(crate) trait Resolver {
    fn model(&self) -> &Model;
    /// Static (upper-bound atom) type of an expression in the current scope; `None` when it cannot be computed.
    fn rty(&mut self, e: &RExpr) -> Option<TupleSet>;

    /// Does candidate `c` fit the expected type?
    fn compatible(&mut self, c: &RExpr, exp: &Exp) -> bool {
        if matches!(exp, Exp::Any) {
            return true;
        }
        let Some(t) = self.rty(c) else { return true };
        match exp {
            Exp::Any => true,
            Exp::Same(w) => t.arity == w.arity && t.tuples.iter().any(|x| w.tuples.contains(x)),
            Exp::JoinRight(cols) => t.tuples.iter().any(|x| cols.contains(&x[0])),
            Exp::JoinLeft(cols) => t.tuples.iter().any(|x| cols.contains(&x[x.len() - 1])),
        }
    }

    fn resolve(&mut self, e: &RExpr, exp: &Exp) -> Result<RExpr, AlloyError> {
        match e {
            RExpr::Block(items) if items.len() == 1 => self.resolve(&items[0], exp),
            RExpr::Choice(cands) => {
                let mut keep = Vec::new();
                let mut marked: Vec<bool> = Vec::new();
                for c in cands {
                    let (c, is_marked) = match c {
                        RExpr::Choice(v) if v.len() == 1 => (&v[0], true),
                        other_c => (other_c, false),
                    };
                    let c = match c {
                        RExpr::Call(fid, args) => {
                            let params = self.model().funcs[*fid as usize].params.clone();
                            if params.len() != args.len() {
                                continue;
                            }
                            let mut new_args = Vec::new();
                            let mut ok = true;
                            for (a, (_, pb)) in args.iter().zip(&params) {
                                let e2 = Exp::same_or_any(self.rty(pb));
                                match self.resolve(a, &e2) {
                                    Ok(r) => {
                                        if is_choice(&r) || self.compatible(&r, &e2) {
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
                        // a join candidate whose type is empty (or ill-formed) is never an exact match (Java: EMPTY type)
                        RExpr::Bin(BinOp::Join, ..)
                            if self.rty(c).map_or(true, |t| t.tuples.is_empty()) =>
                        {
                            continue
                        }
                        other_c => other_c.clone(),
                    };
                    if self.compatible(&c, exp) {
                        keep.push(c);
                        marked.push(is_marked);
                    }
                }
                // lowest penalty wins
                if marked.iter().any(|m| !*m) && marked.iter().any(|m| *m) {
                    let mut k = Vec::new();
                    for (c, m) in keep.into_iter().zip(&marked) {
                        if !*m {
                            k.push(c);
                        }
                    }
                    keep = k;
                }
                match keep.len() {
                    0 => {
                        // No exact match: Java keeps the candidates of the right arity ("legal matches"). Two or
                        // more that are all empty of the same arity resolve to `none` (ExprChoice.resolveHelper);
                        // otherwise any of them gives the same (empty, warned) result.
                        let mut legal: Vec<(RExpr, Option<TupleSet>)> = Vec::new();
                        for c in cands {
                            let inner = match c {
                                RExpr::Choice(v) if v.len() == 1 => &v[0],
                                other_c => other_c,
                            };
                            let t = self.rty(inner);
                            let shape_ok = match (exp, &t) {
                                (Exp::Same(w), Some(ty)) => ty.arity == w.arity,
                                _ => true,
                            };
                            if shape_ok {
                                legal.push((inner.clone(), t));
                            }
                        }
                        if legal.len() > 1 {
                            let ar = legal[0].1.as_ref().map(|t| t.arity);
                            let all_empty = legal.iter().all(|(_, t)| matches!(t, Some(t) if t.tuples.is_empty() && Some(t.arity) == ar));
                            if let (true, Some(ar)) = (all_empty, ar) {
                                let none = || RExpr::Sig(alloy_core::sema::SIG_NONE);
                                let mut ans = none();
                                for _ in 1..ar {
                                    ans = RExpr::Bin(BinOp::Arrow(alloy_core::syntax::Mult::Set, alloy_core::syntax::Mult::Set), Box::new(ans), Box::new(none()));
                                }
                                return Ok(ans);
                            }
                        }
                        if let Some((c, _)) = legal.into_iter().next() {
                            return if is_choice(&c) { self.resolve(&c, exp) } else { Ok(c) };
                        }
                        let desc = format!("{:.300}", format!("{:?}", cands));
                        Err(err(format!(
                            "no overloaded candidate matches the expected type: {desc}"
                        )))
                    }
                    // Java: the single match is resolved further (`ch.get(0).resolve(t)`)
                    1 => {
                        let c = keep.remove(0);
                        if is_choice(&c) {
                            self.resolve(&c, exp)
                        } else {
                            Ok(c)
                        }
                    }
                    _ => Ok(RExpr::Choice(keep)),
                }
            }
            RExpr::Bin(op @ (BinOp::Plus | BinOp::Intersect | BinOp::Override), a, b)
                if is_choice(e) =>
            {
                let a2 = self.resolve(a, exp)?;
                let b2 = self.resolve(b, exp)?;
                let (a2, b2) = self.resolve_pair(&a2, &b2)?;
                Ok(RExpr::Bin(*op, Box::new(a2), Box::new(b2)))
            }
            RExpr::Bin(BinOp::Minus, a, b) if is_choice(e) => {
                let a2 = self.resolve(a, exp)?;
                let b2 = self.resolve_pair(&a2, b)?.1;
                Ok(RExpr::Bin(BinOp::Minus, Box::new(a2), Box::new(b2)))
            }
            RExpr::Bin(BinOp::Join, a, b) if is_choice(e) => {
                let (a2, b2) = self.resolve_join(a, b)?;
                let j = RExpr::Bin(BinOp::Join, Box::new(a2), Box::new(b2));
                if matches!(exp, Exp::Any) || !is_choice(&j) {
                    return Ok(j);
                }
                // still overloaded: keep the alternatives whose joined type fits the expected type
                let Some(alts) = alternatives(&j) else {
                    return Ok(j);
                };
                let n = alts.len();
                let mut keep = Vec::new();
                for x in alts {
                    if self.compatible(&unmark(&x), exp) {
                        keep.push(x);
                    }
                }
                match keep.len() {
                    1 => self.resolve(&keep.remove(0), exp),
                    k if k > 1 && k < n => Ok(RExpr::Choice(keep)),
                    _ => Ok(j),
                }
            }
            RExpr::Un(UnOp::Transpose, x) if is_choice(e) => {
                let flipped = match exp {
                    Exp::Any => Exp::Any,
                    Exp::Same(w) => Exp::Same(TupleSet::from_tuples(
                        w.arity,
                        w.tuples
                            .iter()
                            .map(|t| t.iter().rev().copied().collect::<Vec<_>>()),
                    )),
                    Exp::JoinRight(c) => Exp::JoinLeft(c.clone()),
                    Exp::JoinLeft(c) => Exp::JoinRight(c.clone()),
                };
                Ok(RExpr::Un(
                    UnOp::Transpose,
                    Box::new(self.resolve(x, &flipped)?),
                ))
            }
            RExpr::Un(op @ (UnOp::Closure | UnOp::ReflClosure | UnOp::Set), x) if is_choice(e) => {
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

    /// Resolves the overloaded operands of a binary operator against each other (same arity/overlapping types).
    fn resolve_pair(&mut self, a: &RExpr, b: &RExpr) -> Result<(RExpr, RExpr), AlloyError> {
        let (mut a, mut b) = (a.clone(), b.clone());
        if is_choice(&a) {
            let exp = if is_choice(&b) { None } else { self.rty(&b) };
            a = self.resolve(&a, &Exp::same_or_any(exp))?;
        }
        if is_choice(&b) {
            let exp = self.rty(&a);
            b = self.resolve(&b, &Exp::same_or_any(exp))?;
        }
        if is_choice(&a) && !is_choice(&b) {
            let exp = self.rty(&b);
            a = self.resolve(&a, &Exp::same_or_any(exp))?;
        }
        Ok((a, b))
    }

    /// Overloads of `a <: r` (domain = true: `a` against the first column of `r`) and `r :> b`.
    fn resolve_restrict(
        &mut self,
        a: &RExpr,
        b: &RExpr,
        domain: bool,
    ) -> Result<(RExpr, RExpr), AlloyError> {
        let (mut a, mut b) = (a.clone(), b.clone());
        if domain {
            if is_choice(&b) {
                let exp = self
                    .rty(&a)
                    .map(|t| Exp::JoinRight(t.tuples.iter().map(|x| x[0]).collect()));
                b = self.resolve(&b, &exp.unwrap_or(Exp::Any))?;
            }
        } else if is_choice(&a) {
            let exp = self
                .rty(&b)
                .map(|t| Exp::JoinLeft(t.tuples.iter().map(|x| x[0]).collect()));
            a = self.resolve(&a, &exp.unwrap_or(Exp::Any))?;
        }
        Ok((a, b))
    }

    /// Resolves the operands of a join `a.b`: last column of `a` against first column of `b`.
    fn resolve_join(&mut self, a: &RExpr, b: &RExpr) -> Result<(RExpr, RExpr), AlloyError> {
        let (mut a, mut b) = (a.clone(), b.clone());
        if is_choice(&a) && !is_choice(&b) {
            let exp = self
                .rty(&b)
                .map(|t| Exp::JoinLeft(t.tuples.iter().map(|x| x[0]).collect()));
            a = self.resolve(&a, &exp.unwrap_or(Exp::Any))?;
        }
        if is_choice(&b) {
            let exp = self
                .rty(&a)
                .map(|t| Exp::JoinRight(t.tuples.iter().map(|x| x[x.len() - 1]).collect()));
            b = self.resolve(&b, &exp.unwrap_or(Exp::Any))?;
        }
        if is_choice(&a) {
            let exp = self
                .rty(&b)
                .map(|t| Exp::JoinLeft(t.tuples.iter().map(|x| x[0]).collect()));
            a = self.resolve(&a, &exp.unwrap_or(Exp::Any))?;
        }
        Ok((a, b))
    }

    /// `ExprList.resolve` for `pred/totalOrder[elem, first, next]`: `first` against elem's type, `next` against
    /// elem->elem.
    fn resolve_total_order(&mut self, args: &[RExpr]) -> Result<Vec<RExpr>, AlloyError> {
        let mut out = args.to_vec();
        if out.len() != 3 || !out.iter().any(is_choice) {
            return Ok(out);
        }
        if is_choice(&out[0]) {
            out[0] = self.resolve(&out[0], &Exp::Any)?;
        }
        if let Some(t) = self.rty(&out[0]) {
            if is_choice(&out[1]) {
                out[1] = self.resolve(&out[1], &Exp::Same(t.clone()))?;
            }
            if is_choice(&out[2]) {
                let pairs: Vec<Vec<u32>> =
                    t.tuples.iter().flat_map(|a| t.tuples.iter().map(move |b| vec![a[0], b[0]])).collect();
                let tt = TupleSet::from_tuples(2, pairs);
                out[2] = self.resolve(&out[2], &Exp::Same(tt))?;
            }
        }
        Ok(out)
    }

    /// `ExprList.resolve` for `disj[a, b, ..]`: every argument against the union of the arguments' types.
    fn resolve_disj(&mut self, args: &[RExpr]) -> Result<Vec<RExpr>, AlloyError> {
        if !args.iter().any(is_choice) {
            return Ok(args.to_vec());
        }
        let mut p: Option<TupleSet> = None;
        for a in args {
            if is_choice(a) {
                continue;
            }
            if let Some(t) = self.rty(a) {
                p = Some(match p {
                    None => t,
                    Some(x) if x.arity == t.arity => TupleSet::from_tuples(x.arity, x.tuples.iter().chain(t.tuples.iter()).cloned()),
                    Some(x) => x,
                });
            }
        }
        let exp = p.map_or(Exp::Any, Exp::Same);
        let mut out = Vec::with_capacity(args.len());
        for a in args {
            out.push(if is_choice(a) { self.resolve(a, &exp)? } else { a.clone() });
        }
        Ok(out)
    }
}
