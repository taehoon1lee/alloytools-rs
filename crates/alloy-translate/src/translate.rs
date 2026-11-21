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
use kodkod::ast::{Const as KConst, Decl, Expr, Formula, Multiplicity, Quantifier};
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

    // Relations of the sigs: lower = exact atoms, upper = atoms the sig may take.
    let mut sig_rel: Vec<Option<u32>> = vec![None; model.sigs.len()];
    for (i, s) in model.sigs.iter().enumerate() {
        if s.kind != SigKind::User {
            continue;
        }
        let up = sig_upper(model, &lay, i as SigId, n_atoms)?;
        let lo = lay.lower(i as SigId);
        let upper = unary(up);
        let lower = unary(lo);
        let id = bounds.bound(&s.label, lower, upper).map_err(other)?;
        sig_rel[i] = Some(id);
    }
    // Relations of the fields: upper = owner × (type of the declaration).
    let mut field_rel: Vec<Option<u32>> = vec![None; model.fields.len()];
    for (fi, f) in model.fields.iter().enumerate() {
        let owner_up = unary(sig_upper(model, &lay, f.owner, n_atoms)?);
        let decl_ty = type_of(model, &lay, n_atoms, &f.decl)?;
        let upper = owner_up.product(&decl_ty);
        let lower = TupleSet::empty(upper.arity);
        let id = bounds.bound(&f.label, lower, upper).map_err(other)?;
        field_rel[fi] = Some(id);
    }

    let mut tr = Tr {
        model,
        lay: &lay,
        sig_rel,
        int_rel,
        field_rel,
        locals: HashMap::new(),
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

    let command = tr.formula(&cmd.formula)?;
    conjuncts.push(if cmd.check { Formula::Not(Box::new(command)) } else { command });
    Ok(Problem {
        bounds,
        formula: Formula::And(conjuncts),
    })
}

/// Names of the integer atoms of a bitwidth: `-2^(b-1) ..= 2^(b-1)-1` (empty for bitwidth 0).
fn int_atom_names(bitwidth: i32) -> Vec<String> {
    if bitwidth <= 0 {
        return Vec::new();
    }
    let half = 1i64 << (bitwidth - 1);
    (-half..half).map(|v| v.to_string()).collect()
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

/// Type (upper-bound tuples) of a declaration expression, used for field bounds.
fn type_of(model: &Model, lay: &Layout, n_atoms: u32, e: &RExpr) -> Result<TupleSet, AlloyError> {
    Ok(match e {
        RExpr::Sig(s) => unary(sig_upper(model, lay, *s, n_atoms)?),
        RExpr::Const(Const::Univ) => unary((0..n_atoms).collect()),
        RExpr::Const(Const::None) => TupleSet::empty(1),
        RExpr::Un(UnOp::Set | UnOp::One | UnOp::Lone | UnOp::Some, x) => type_of(model, lay, n_atoms, x)?,
        RExpr::Bin(BinOp::Plus, a, b) => type_of(model, lay, n_atoms, a)?.union(&type_of(model, lay, n_atoms, b)?),
        RExpr::Bin(BinOp::Intersect, a, b) => {
            let (a, b) = (type_of(model, lay, n_atoms, a)?, type_of(model, lay, n_atoms, b)?);
            TupleSet {
                arity: a.arity,
                tuples: a.tuples.intersection(&b.tuples).cloned().collect(),
            }
        }
        RExpr::Bin(BinOp::Minus, a, b) => type_of(model, lay, n_atoms, a)?.difference(&type_of(model, lay, n_atoms, b)?),
        RExpr::Bin(BinOp::Arrow(_, _), a, b) => type_of(model, lay, n_atoms, a)?.product(&type_of(model, lay, n_atoms, b)?),
        RExpr::Bin(BinOp::Join, a, b) => join_ts(&type_of(model, lay, n_atoms, a)?, &type_of(model, lay, n_atoms, b)?)?,
        _ => return Err(unsupported("declaration type that is not a sig expression")),
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

struct Tr<'a> {
    model: &'a Model,
    lay: &'a Layout,
    sig_rel: Vec<Option<u32>>,
    /// The `Int` relation (exactly the integer atoms).
    int_rel: u32,
    field_rel: Vec<Option<u32>>,
    /// Alloy locals (quantifier variables, parameters, `let`s) -> kodkod expressions.
    locals: HashMap<LocalId, Expr>,
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
            _ => match self.sig_rel.get(s as usize).copied().flatten() {
                Some(r) => Ok(Expr::Rel(r)),
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
            RExpr::Const(other_c) => {
                return Err(unsupported(format!("constant {other_c:?} (integers/temporal)")))
            }
            RExpr::Num(_) => return Err(unsupported("integer literal (integers not ported yet)")),
            RExpr::Un(UnOp::Set, x) => self.expr(x)?,
            RExpr::Un(UnOp::Transpose, x) => Expr::Transpose(Box::new(self.expr(x)?)),
            RExpr::Un(UnOp::Closure, x) => Expr::Closure(Box::new(self.expr(x)?)),
            RExpr::Un(UnOp::ReflClosure, x) => Expr::ReflexiveClosure(Box::new(self.expr(x)?)),
            RExpr::Un(op, _) => return Err(unsupported(format!("unary operator {op:?} in expression position"))),
            RExpr::Bin(BinOp::Join, a, b) => Expr::join(self.expr(a)?, self.expr(b)?),
            RExpr::Bin(BinOp::Plus, a, b) => Expr::union(self.expr(a)?, self.expr(b)?),
            RExpr::Bin(BinOp::Minus, a, b) => Expr::Difference(Box::new(self.expr(a)?), Box::new(self.expr(b)?)),
            RExpr::Bin(BinOp::Intersect, a, b) => Expr::Intersection(Box::new(self.expr(a)?), Box::new(self.expr(b)?)),
            RExpr::Bin(BinOp::Override, a, b) => Expr::Override(Box::new(self.expr(a)?), Box::new(self.expr(b)?)),
            RExpr::Bin(BinOp::Arrow(Mult::Set, Mult::Set), a, b) => Expr::product(self.expr(a)?, self.expr(b)?),
            RExpr::Bin(BinOp::Arrow(_, _), _, _) => {
                return Err(unsupported("arrow multiplicities outside a field declaration (M5.3)"))
            }
            RExpr::Bin(BinOp::DomainRestrict, a, b) => {
                // a <: r = (a -> univ^(k)) & r, k = arity(r) - 1
                let (a, r) = (self.expr(a)?, self.expr(b)?);
                let k = self.arity(&r)? - 1;
                Expr::Intersection(Box::new(Expr::product(a, self.univ_pow(k))), Box::new(r))
            }
            RExpr::Bin(BinOp::RangeRestrict, r, b) => {
                // r :> b = (univ^(k) -> b) & r, k = arity(r) - 1
                let (r, b) = (self.expr(r)?, self.expr(b)?);
                let k = self.arity(&r)? - 1;
                Expr::Intersection(Box::new(Expr::product(self.univ_pow(k), b)), Box::new(r))
            }
            RExpr::Bin(op, _, _) => return Err(unsupported(format!("binary operator {op:?} in expression position"))),
            RExpr::Compr(decls, body) => {
                let (kdecls, disj) = self.decls(decls)?;
                let f = self.formula(body)?;
                let f = with_disjointness(f, &disj);
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
            RExpr::Choice(_) => return Err(unsupported("overloaded name (ExprChoice, M3.4)")),
            RExpr::Quant(..) | RExpr::Block(_) | RExpr::Disj(_) | RExpr::TotalOrder(_) => {
                return Err(other("formula used where an expression is expected"))
            }
        })
    }

    /// Formula of an Alloy formula expression.
    fn formula(&mut self, e: &RExpr) -> Result<Formula, AlloyError> {
        Ok(match e {
            RExpr::Block(items) => Formula::And(items.iter().map(|x| self.formula(x)).collect::<Result<_, _>>()?),
            RExpr::Bin(BinOp::And, a, b) => Formula::And(vec![self.formula(a)?, self.formula(b)?]),
            RExpr::Bin(BinOp::Or, a, b) => Formula::Or(vec![self.formula(a)?, self.formula(b)?]),
            RExpr::Bin(BinOp::Implies, a, b) => Formula::Implies(Box::new(self.formula(a)?), Box::new(self.formula(b)?)),
            RExpr::Bin(BinOp::Iff, a, b) => Formula::Iff(Box::new(self.formula(a)?), Box::new(self.formula(b)?)),
            RExpr::Bin(BinOp::Equals, a, b) => Formula::Equal(self.expr(a)?, self.expr(b)?),
            RExpr::Bin(BinOp::In, a, b) => Formula::Subset(self.expr(a)?, self.expr(b)?),
            RExpr::Bin(op @ (BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge), _, _) => {
                return Err(unsupported(format!("integer comparison {op:?} (integers not ported yet)")))
            }
            RExpr::Un(UnOp::Not, x) => Formula::Not(Box::new(self.formula(x)?)),
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
            RExpr::TotalOrder(_) => return Err(unsupported("pred/totalOrder (M5.4)")),
            RExpr::Choice(cands) if cands.len() == 1 => self.formula(&cands[0])?,
            RExpr::Choice(_) => return Err(unsupported("overloaded name (ExprChoice, M3.4)")),
            other_e => {
                return Err(other(format!("expression used as a formula: {:?}", kind_name(other_e))))
            }
        })
    }

    fn quantified(&mut self, q: Quant, decls: &[RDecl], body: &RExpr) -> Result<Formula, AlloyError> {
        let (kdecls, disj) = self.decls(decls)?;
        let b = self.formula(body)?;
        let b = with_disjointness(b, &disj);
        Ok(match q {
            Quant::All => Formula::Quantified(Quantifier::All, kdecls, Box::new(b)),
            Quant::Some => Formula::Quantified(Quantifier::Some, kdecls, Box::new(b)),
            Quant::No => Formula::Not(Box::new(Formula::Quantified(Quantifier::Some, kdecls, Box::new(b)))),
            Quant::Lone | Quant::One => {
                // "at most one": for all x,y in dom: f(x) & f(y) => x = y. Needs one copy per variable.
                if decls.iter().map(|d| d.vars.len()).sum::<usize>() != 1 {
                    return Err(unsupported("lone/one quantifier over several variables (M5.4)"));
                }
                let (kdecls2, _) = self.decls(decls)?;
                let x = kdecls[0].var;
                let y = kdecls2[0].var;
                let bx = b.clone();
                let by = self.formula(body)?;
                let by = with_disjointness(by, &disj);
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

    /// Declares the variables of `decls` (one kodkod variable per Alloy variable) and returns the
    /// kodkod declarations plus the `disj` groups as lists of variable ids.
    fn decls(&mut self, decls: &[RDecl]) -> Result<(Vec<Decl>, Vec<Vec<u32>>), AlloyError> {
        let mut out = Vec::new();
        let mut disj = Vec::new();
        for d in decls {
            let domain = self.expr(&d.bound)?;
            let mut group = Vec::new();
            for &l in &d.vars {
                let v = self.fresh();
                let a = self.arity(&domain)?;
                self.local_arity.insert(v, a);
                self.locals.insert(l, Expr::Var(v));
                out.push(Decl {
                    var: v,
                    domain: domain.clone(),
                    disjoint: d.disjoint,
                });
                group.push(v);
            }
            if d.disjoint && group.len() > 1 {
                disj.push(group);
            }
        }
        Ok((out, disj))
    }

    fn bind_lets(&mut self, binds: &[(LocalId, RExpr)]) -> Result<Vec<(LocalId, Option<Expr>)>, AlloyError> {
        let mut saved = Vec::new();
        for (l, e) in binds {
            let v = self.expr(e)?;
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
            return Err(other("call with the wrong number of arguments"));
        }
        if self.depth >= MAX_CALL_DEPTH {
            return Err(unsupported("recursive predicate/function (too deep to inline)"));
        }
        let mut vals = Vec::new();
        for a in args {
            vals.push(self.expr(a)?);
        }
        let mut saved = Vec::new();
        for ((l, _), v) in params.iter().zip(vals) {
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
        let mut out = Vec::new();
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
            } else if let Some(p) = sig.parent {
                out.push(Formula::Subset(me.clone(), self.sig_expr(p)?));
            }
            // Subsigs of one parent are disjoint.
            let kids: Vec<SigId> = self.lay.children(i as SigId).to_vec();
            for a in 0..kids.len() {
                for b in a + 1..kids.len() {
                    let inter = Expr::Intersection(
                        Box::new(self.sig_expr(kids[a])?),
                        Box::new(self.sig_expr(kids[b])?),
                    );
                    out.push(Formula::Multiplicity(Multiplicity::No, inter));
                }
            }
            // An abstract sig is exactly the union of its children.
            if sig.is_abstract {
                let mut parts = Vec::new();
                for &k in &kids {
                    parts.push(self.sig_expr(k)?);
                }
                let rhs = parts
                    .into_iter()
                    .reduce(Expr::union)
                    .unwrap_or(Expr::Const(KConst::None));
                out.push(Formula::Equal(me.clone(), rhs));
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
            // Arrow declaration `f: L m1 -> m2 R`: multiplicities apply per domain element.
            if let RExpr::Bin(BinOp::Arrow(ml, mr), l, r) = &f.decl {
                let lexpr = self.expr(l)?;
                let rexpr = self.expr(r)?;
                let product = Expr::product(lexpr.clone(), rexpr.clone());
                out.push(Formula::Subset(rel.clone(), Expr::product(owner.clone(), product)));
                let this = self.fresh();
                let a = self.fresh();
                let (ta, tb) = (self.arity(&lexpr)?, self.arity(&rexpr)?);
                if ta != 1 || tb != 1 {
                    return Err(unsupported("arrow multiplicity on non-unary columns (M5.3)"));
                }
                // all this: owner, a: L | m2 (this.f).a
                if let Some(m) = mult_of(Some(*mr)) {
                    let img = Expr::join(Expr::join(Expr::Var(this), rel.clone()), Expr::Var(a));
                    out.push(Formula::Quantified(
                        Quantifier::All,
                        vec![
                            Decl { var: this, domain: owner.clone(), disjoint: false },
                            Decl { var: a, domain: lexpr.clone(), disjoint: false },
                        ],
                        Box::new(Formula::Multiplicity(m, img)),
                    ));
                }
                // all this: owner, b: R | m1 (this.f).b
                if let Some(m) = mult_of(Some(*ml)) {
                    let this2 = self.fresh();
                    let b2 = self.fresh();
                    let img = Expr::join(Expr::join(Expr::Var(this2), rel.clone()), Expr::Var(b2));
                    out.push(Formula::Quantified(
                        Quantifier::All,
                        vec![
                            Decl { var: this2, domain: owner.clone(), disjoint: false },
                            Decl { var: b2, domain: rexpr.clone(), disjoint: false },
                        ],
                        Box::new(Formula::Multiplicity(m, img)),
                    ));
                }
                continue;
            }
            // Plain declaration `f: m E`: f in owner -> E, and m (this.f) per owner atom.
            let decl = self.expr(&f.decl)?;
            out.push(Formula::Subset(rel.clone(), Expr::product(owner.clone(), decl)));
            if let Some(m) = f.mult.and_then(|m| mult_of(Some(m))) {
                let this = self.fresh();
                let img = Expr::join(Expr::Var(this), rel.clone());
                out.push(Formula::Quantified(
                    Quantifier::All,
                    vec![Decl { var: this, domain: owner, disjoint: false }],
                    Box::new(Formula::Multiplicity(m, img)),
                ));
            }
        }
        Ok(out)
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
fn with_disjointness(b: Formula, groups: &[Vec<u32>]) -> Formula {
    let mut parts = Vec::new();
    for g in groups {
        for i in 0..g.len() {
            for j in i + 1..g.len() {
                parts.push(Formula::Not(Box::new(Formula::Equal(Expr::Var(g[i]), Expr::Var(g[j])))));
            }
        }
    }
    if parts.is_empty() {
        b
    } else {
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
