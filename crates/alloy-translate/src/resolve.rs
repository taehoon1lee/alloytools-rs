//! Port of `edu.mit.csail.sdg.ast.ExprChoice.resolve` (type-directed overload resolution), shared by the fast
//! translator (`translate.rs`) and the exact pipeline (`exact/`). Types are atom-level upper bounds (`type_of`).
//! Candidates that do not fit the expected type are dropped; overloaded calls also need their (resolved) arguments
//! to fit the parameter types; several survivors stay a `Choice`. The expected type is propagated through joins
//! (Java resolves top-down: `ExprBinary.resolve` then `ExprChoice.resolve`).

use alloy_core::error::{AlloyError, ErrorKind};
use alloy_core::sema::{Model, RExpr};
use alloy_core::syntax::{BinOp, UnOp};
use kodkod::instance::TupleSet;

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
}
