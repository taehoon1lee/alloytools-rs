//! Port of the parts of `edu.mit.csail.sdg.ast.Type` (sig-level relational types) and of
//! `CompModule.applicable` that decide which overloaded function calls are legal.
//!
//! After name resolution (`sema`), Java has typed every expression; a call whose argument types cannot fit the
//! parameter types is an `ExprBadCall`: it is never chosen among overloads, and when no candidate is left the file
//! has a type error ("This cannot be a correct call"). [`check_calls`] reproduces that with Java's types.
//! Types that cannot be computed here are treated as unknown, which keeps the candidate (never a spurious error).

use std::collections::HashMap;

use crate::error::{AlloyError, ErrorKind};
use crate::sema::{FieldId, FuncId, LocalId, Model, RExpr, SigId, SIG_INT, SIG_NONE, SIG_SEQINT, SIG_STRING, SIG_UNIV};
use crate::syntax::{BinOp, Const, Quant, UnOp};

/// `ast.Type` restricted to relational product types.
#[derive(Clone, Debug, PartialEq, Default)]
pub struct JType {
    pub entries: Vec<Vec<SigId>>,
}

impl JType {
    /// `Type.hasTuple`: some product type has no `none` column.
    pub fn has_tuple(&self) -> bool {
        self.entries.iter().any(|e| !e.is_empty() && !e.contains(&SIG_NONE))
    }
    pub fn has_common_arity(&self, o: &JType) -> bool {
        self.entries.iter().any(|a| o.entries.iter().any(|b| a.len() == b.len()))
    }
}

/// The prim-sig hierarchy as Java sees it (UNIV is the parent of every top-level sig, Int and String).
pub struct Hier<'a> {
    pub model: &'a Model,
}

impl Hier<'_> {
    fn parent(&self, s: SigId) -> Option<SigId> {
        match s {
            SIG_UNIV | SIG_NONE => None,
            SIG_INT | SIG_STRING => Some(SIG_UNIV),
            SIG_SEQINT => Some(SIG_INT),
            _ => Some(self.model.sigs[s as usize].parent.unwrap_or(SIG_UNIV)),
        }
    }
    /// `PrimSig.isSameOrDescendentOf`
    pub fn same_or_desc(&self, a: SigId, b: SigId) -> bool {
        if a == SIG_NONE || a == b || b == SIG_UNIV {
            return true;
        }
        if a == SIG_UNIV || b == SIG_NONE {
            return false;
        }
        let mut me = Some(a);
        while let Some(x) = me {
            if x == b {
                return true;
            }
            me = self.parent(x);
        }
        false
    }
    fn isect(&self, a: SigId, b: SigId) -> SigId {
        if self.same_or_desc(a, b) {
            a
        } else if self.same_or_desc(b, a) {
            b
        } else {
            SIG_NONE
        }
    }
    fn is_empty_pt(p: &[SigId]) -> bool {
        p.is_empty() || p.contains(&SIG_NONE)
    }
    fn subtype(&self, x: &[SigId], y: &[SigId]) -> bool {
        (0..x.len()).rev().all(|i| self.same_or_desc(x[i], y[i]))
    }
    /// `Type.add(entries, arities, x)`
    fn add(&self, ee: &mut Vec<Vec<SigId>>, x: Vec<SigId>) {
        if x.is_empty() {
            return;
        }
        let arity = x.len();
        let mut n = ee.len();
        let mut i = ee.len();
        while i > 0 {
            i -= 1;
            if ee[i].len() != arity {
                continue;
            }
            if self.subtype(&x, &ee[i]) {
                return;
            }
            if self.subtype(&ee[i], &x) {
                n -= 1;
                ee.swap(i, n);
                ee.truncate(n);
            }
        }
        ee.push(x);
    }
    pub fn make(&self, s: SigId) -> JType {
        JType { entries: vec![vec![s]] }
    }
    pub fn product(&self, a: &JType, b: &JType) -> JType {
        let mut ee = Vec::new();
        for x in &a.entries {
            for y in &b.entries {
                let n = x.len() + y.len();
                let p = if Self::is_empty_pt(x) || Self::is_empty_pt(y) {
                    vec![SIG_NONE; n]
                } else {
                    let mut v = x.clone();
                    v.extend(y.iter().copied());
                    v
                };
                self.add(&mut ee, p);
            }
        }
        JType { entries: ee }
    }
    /// `Type.merge`: every product type of both
    pub fn merge(&self, a: &JType, b: &JType) -> JType {
        let mut ee = a.entries.clone();
        for x in &b.entries {
            self.add(&mut ee, x.clone());
        }
        JType { entries: ee }
    }
    /// `Type.unionWithCommonArity`
    pub fn union(&self, a: &JType, b: &JType) -> JType {
        let has = |t: &JType, n: usize| t.entries.iter().any(|e| e.len() == n);
        let mut ee = Vec::new();
        for x in &a.entries {
            if has(b, x.len()) {
                self.add(&mut ee, x.clone());
            }
        }
        for x in &b.entries {
            if has(a, x.len()) {
                self.add(&mut ee, x.clone());
            }
        }
        JType { entries: ee }
    }
    pub fn intersect(&self, a: &JType, b: &JType) -> JType {
        let mut ee = Vec::new();
        for x in &a.entries {
            for y in &b.entries {
                if x.len() == y.len() {
                    let mut v: Vec<SigId> = x.iter().zip(y.iter()).map(|(&p, &q)| self.isect(p, q)).collect();
                    if v.contains(&SIG_NONE) {
                        v = vec![SIG_NONE; x.len()];
                    }
                    self.add(&mut ee, v);
                }
            }
        }
        JType { entries: ee }
    }
    /// `Type.intersects`
    pub fn intersects(&self, a: &JType, b: &JType) -> bool {
        a.entries.iter().any(|x| {
            b.entries.iter().any(|y| {
                x.len() == y.len()
                    && !Self::is_empty_pt(x)
                    && !Self::is_empty_pt(y)
                    && x.iter().zip(y.iter()).all(|(&p, &q)| self.isect(p, q) != SIG_NONE)
            })
        })
    }
    pub fn join(&self, a: &JType, b: &JType) -> JType {
        let mut ee = Vec::new();
        for x in &a.entries {
            for y in &b.entries {
                if x.len() > 1 || y.len() > 1 {
                    let n = x.len() + y.len() - 2;
                    let c = self.isect(*x.last().unwrap(), y[0]);
                    let p = if c == SIG_NONE || Self::is_empty_pt(x) || Self::is_empty_pt(y) {
                        vec![SIG_NONE; n]
                    } else {
                        let mut v = x[..x.len() - 1].to_vec();
                        v.extend(y[1..].iter().copied());
                        v
                    };
                    self.add(&mut ee, p);
                }
            }
        }
        JType { entries: ee }
    }
    pub fn transpose(&self, a: &JType) -> JType {
        let mut ee = Vec::new();
        for x in &a.entries {
            if x.len() == 2 {
                self.add(&mut ee, vec![x[1], x[0]]);
            }
        }
        JType { entries: ee }
    }
    pub fn closure(&self, a: &JType) -> JType {
        let mut ans = JType { entries: a.entries.iter().filter(|e| e.len() == 2).cloned().collect() };
        let u = ans.clone();
        let mut uu = u.clone();
        for _ in 0..64 {
            uu = self.join(&uu, &u);
            let old = ans.clone();
            ans = self.union(&ans, &uu);
            if old == ans {
                break;
            }
        }
        ans
    }
    /// `Sig.type()`: a subset sig has the union of its parents' types
    pub fn sig_type(&self, s: SigId) -> JType {
        if s <= SIG_SEQINT || self.model.sigs[s as usize].subset_of.is_empty() {
            return self.make(s);
        }
        let mut t = JType::default();
        for &p in &self.model.sigs[s as usize].subset_of {
            if p == s {
                continue;
            }
            let pt = self.sig_type(p);
            t = self.merge(&t, &pt);
        }
        t
    }
}

/// Java type of a resolved expression (only what overload legality needs).
#[derive(Clone, Debug)]
enum T {
    Rel(JType),
    Int,
    Bool,
}

struct Typer<'a> {
    h: Hier<'a>,
    env: Vec<(LocalId, Option<JType>)>,
    fields: HashMap<FieldId, Option<JType>>,
    rets: HashMap<FuncId, Option<JType>>,
    busy: Vec<FuncId>,
}

fn strip_mult(e: &RExpr) -> &RExpr {
    match e {
        RExpr::Un(UnOp::Set | UnOp::One | UnOp::Lone | UnOp::Some | UnOp::ExactlyOf, x) => strip_mult(x),
        RExpr::Block(v) if v.len() == 1 => strip_mult(&v[0]),
        other => other,
    }
}

impl Typer<'_> {
    fn rel(&mut self, e: &RExpr) -> Option<JType> {
        match self.ty(e)? {
            T::Rel(t) => Some(t),
            T::Int => Some(self.h.make(SIG_INT)),
            T::Bool => None,
        }
    }
    fn local(&self, l: LocalId) -> Option<JType> {
        self.env.iter().rev().find(|(x, _)| *x == l).and_then(|(_, t)| t.clone())
    }
    fn field(&mut self, f: FieldId) -> Option<JType> {
        if let Some(t) = self.fields.get(&f) {
            return t.clone();
        }
        self.fields.insert(f, None); // recursion guard
        let fd = &self.h.model.fields[f as usize];
        let (owner, this_l, decl) = (fd.owner, fd.this_local, fd.decl.clone());
        let ot = self.h.sig_type(owner);
        self.env.push((this_l, Some(ot.clone())));
        let dt = self.decl_type(&decl);
        self.env.pop();
        let t = dt.map(|d| self.h.product(&ot, &d));
        self.fields.insert(f, t.clone());
        t
    }
    fn decl_type(&mut self, b: &RExpr) -> Option<JType> {
        match b {
            RExpr::Un(UnOp::Seq, x) => {
                let t = self.rel(strip_mult(x))?;
                Some(self.h.product(&self.h.make(SIG_SEQINT), &t))
            }
            _ => self.rel(strip_mult(b)),
        }
    }
    /// return type of a function (`returnDecl.type()`, typed with the parameter types)
    fn ret(&mut self, fid: FuncId) -> Option<JType> {
        if let Some(t) = self.rets.get(&fid) {
            return t.clone();
        }
        if self.busy.contains(&fid) {
            return None;
        }
        self.busy.push(fid);
        let func = &self.h.model.funcs[fid as usize];
        let (params, ret) = (func.params.clone(), func.ret.clone());
        let old = self.env.len();
        for (l, b) in &params {
            let t = self.decl_type(b);
            self.env.push((*l, t));
        }
        let t = ret.as_ref().and_then(|r| self.decl_type(r));
        self.env.truncate(old);
        self.busy.pop();
        self.rets.insert(fid, t.clone());
        t
    }
    fn ty(&mut self, e: &RExpr) -> Option<T> {
        let h = &self.h;
        Some(match e {
            RExpr::Sig(s) => T::Rel(h.sig_type(*s)),
            RExpr::Field(f) => T::Rel(self.field(*f)?),
            RExpr::Local(l) => T::Rel(self.local(*l)?),
            RExpr::Const(c) => match c {
                Const::Univ => T::Rel(h.make(SIG_UNIV)),
                Const::None => T::Rel(h.make(SIG_NONE)),
                Const::Iden => T::Rel(h.product(&h.make(SIG_UNIV), &h.make(SIG_UNIV))),
                Const::SigInt => T::Rel(h.make(SIG_INT)),
                Const::SigString => T::Rel(h.make(SIG_STRING)),
                _ => return None,
            },
            RExpr::Num(_) => T::Int,
            RExpr::Str(_) => T::Rel(h.make(SIG_STRING)),
            RExpr::Un(op, x) => match op {
                UnOp::Card | UnOp::IntCast | UnOp::Neg => T::Int,
                UnOp::SigInt => self.ty(x)?,
                UnOp::Transpose => {
                    let t = self.rel(x)?;
                    T::Rel(self.h.transpose(&t))
                }
                UnOp::Closure | UnOp::ReflClosure => {
                    let t = self.rel(x)?;
                    let c = self.h.closure(&t);
                    if *op == UnOp::ReflClosure {
                        let u = self.h.product(&self.h.make(SIG_UNIV), &self.h.make(SIG_UNIV));
                        T::Rel(self.h.merge(&c, &u))
                    } else {
                        T::Rel(c)
                    }
                }
                UnOp::Set | UnOp::ExactlyOf | UnOp::Prime => self.ty(x)?,
                UnOp::Seq => T::Rel(self.decl_type(e)?),
                _ => T::Bool,
            },
            RExpr::Bin(op, a, b) => match op {
                BinOp::Join => {
                    let (x, y) = (self.rel(a)?, self.rel(b)?);
                    T::Rel(self.h.join(&x, &y))
                }
                BinOp::Arrow(..) => {
                    let (x, y) = (self.rel(a)?, self.rel(b)?);
                    T::Rel(self.h.product(&x, &y))
                }
                BinOp::Plus | BinOp::Override => {
                    let (x, y) = (self.rel(a)?, self.rel(b)?);
                    T::Rel(self.h.union(&x, &y))
                }
                BinOp::Intersect => {
                    let (x, y) = (self.rel(a)?, self.rel(b)?);
                    T::Rel(self.h.intersect(&x, &y))
                }
                BinOp::Minus | BinOp::RangeRestrict => T::Rel(self.rel(a)?),
                BinOp::DomainRestrict => T::Rel(self.rel(b)?),
                BinOp::IntPlus | BinOp::IntMinus | BinOp::Mul | BinOp::Div | BinOp::Rem | BinOp::Shl | BinOp::Shr | BinOp::Sha => {
                    T::Int
                }
                _ => T::Bool,
            },
            RExpr::Ite(_, a, b) => match (self.ty(a)?, self.ty(b)?) {
                (T::Rel(x), T::Rel(y)) => T::Rel(self.h.union(&x, &y)),
                (T::Int, T::Int) => T::Int,
                (T::Bool, T::Bool) => T::Bool,
                (T::Int, T::Rel(y)) | (T::Rel(y), T::Int) => T::Rel(self.h.union(&self.h.make(SIG_INT), &y)),
                _ => return None,
            },
            RExpr::Let(binds, body) => {
                let old = self.env.len();
                for (l, x) in binds {
                    let t = self.rel(x);
                    self.env.push((*l, t));
                }
                let r = self.ty(body);
                self.env.truncate(old);
                r?
            }
            RExpr::Call(fid, _) => {
                if self.h.model.funcs[*fid as usize].is_pred {
                    T::Bool
                } else {
                    T::Rel(self.ret(*fid)?)
                }
            }
            RExpr::Block(v) if v.len() == 1 => self.ty(&v[0])?,
            RExpr::Block(_) | RExpr::Disj(_) | RExpr::TotalOrder(_) => T::Bool,
            RExpr::Quant(Quant::Sum, ..) => T::Int,
            RExpr::Quant(..) => T::Bool,
            RExpr::Compr(ds, _) => {
                let old = self.env.len();
                let mut t: Option<JType> = None;
                let mut ok = true;
                for d in ds {
                    let dt = self.decl_type(&d.bound);
                    for &v in &d.vars {
                        self.env.push((v, dt.clone()));
                        match (&t, &dt) {
                            (_, None) => ok = false,
                            (None, Some(x)) => t = Some(x.clone()),
                            (Some(a), Some(x)) => t = Some(self.h.product(a, x)),
                        }
                    }
                }
                self.env.truncate(old);
                if !ok {
                    return None;
                }
                T::Rel(t?)
            }
            RExpr::Choice(c) => {
                let mut t = JType::default();
                for x in c {
                    let xt = self.rel(x)?;
                    t = self.h.merge(&t, &xt);
                }
                T::Rel(t)
            }
        })
    }

    /// `CompModule.applicable(f, args)`
    fn applicable(&mut self, fid: FuncId, args: &[RExpr]) -> bool {
        let params = self.h.model.funcs[fid as usize].params.clone();
        if params.len() != args.len() {
            return params.len() < args.len();
        }
        let old = self.env.len();
        let mut ok = true;
        for ((l, b), a) in params.iter().zip(args) {
            let p = self.decl_type(b);
            self.env.push((*l, p.clone()));
            let (Some(p), Some(a)) = (p, self.rel(a)) else { continue };
            if !a.has_common_arity(&p) || (a.has_tuple() && p.has_tuple() && !self.h.intersects(&a, &p)) {
                ok = false;
                break;
            }
        }
        self.env.truncate(old);
        ok
    }

    /// Visits `e`, removing inapplicable calls from overloads. Returns the label of a call that cannot be legal.
    fn walk(&mut self, e: &mut RExpr, in_choice: bool) -> Result<(), String> {
        match e {
            RExpr::Call(fid, args) => {
                for a in args.iter_mut() {
                    self.walk(a, false)?;
                }
                if !in_choice && !self.applicable(*fid, args) {
                    return Err(self.h.model.funcs[*fid as usize].label.clone());
                }
            }
            RExpr::Choice(cands) => {
                for c in cands.iter_mut() {
                    self.walk(c, true)?;
                }
                if cands.len() > 1 {
                    let mut keep = Vec::new();
                    let mut bad = None;
                    for c in cands.drain(..) {
                        let inner = match &c {
                            RExpr::Choice(v) if v.len() == 1 => &v[0],
                            other => other,
                        };
                        let legal = match inner {
                            RExpr::Call(fid, args) => {
                                let (fid, args) = (*fid, args.clone());
                                let ok = self.applicable(fid, &args);
                                if !ok {
                                    bad = Some(self.h.model.funcs[fid as usize].label.clone());
                                }
                                ok
                            }
                            _ => true,
                        };
                        if legal {
                            keep.push(c);
                        }
                    }
                    if keep.is_empty() {
                        return Err(bad.unwrap_or_default());
                    }
                    if keep.len() == 1 {
                        let only = keep.remove(0);
                        *e = match only {
                            RExpr::Choice(mut v) if v.len() == 1 => v.remove(0),
                            other => other,
                        };
                    } else {
                        *cands = keep;
                    }
                }
            }
            RExpr::Sig(_) | RExpr::Field(_) | RExpr::Local(_) | RExpr::Const(_) | RExpr::Num(_) | RExpr::Str(_) => {}
            RExpr::Un(_, x) => self.walk(x, false)?,
            RExpr::Bin(_, a, b) => {
                self.walk(a, false)?;
                self.walk(b, false)?;
            }
            RExpr::Ite(c, a, b) => {
                self.walk(c, false)?;
                self.walk(a, false)?;
                self.walk(b, false)?;
            }
            RExpr::Let(binds, body) => {
                let old = self.env.len();
                for (l, x) in binds.iter_mut() {
                    self.walk(x, false)?;
                    let t = self.rel(x);
                    self.env.push((*l, t));
                }
                self.walk(body, false)?;
                self.env.truncate(old);
            }
            RExpr::Quant(_, ds, body) | RExpr::Compr(ds, body) => {
                let old = self.env.len();
                for d in ds.iter_mut() {
                    self.walk(&mut d.bound, false)?;
                    let t = self.decl_type(&d.bound);
                    for &v in &d.vars {
                        self.env.push((v, t.clone()));
                    }
                }
                self.walk(body, false)?;
                self.env.truncate(old);
            }
            RExpr::Block(xs) | RExpr::Disj(xs) | RExpr::TotalOrder(xs) => {
                for x in xs.iter_mut() {
                    self.walk(x, false)?;
                }
            }
        }
        Ok(())
    }
}

/// Java's typecheck of calls: drops overloaded calls whose arguments cannot fit (`ExprBadCall`) and reports a
/// type error when a call has no legal candidate left.
pub fn check_calls(model: &mut Model) -> Result<(), AlloyError> {
    // the typer reads sigs, fields, parameters and return types; the bodies it rewrites are taken out meanwhile
    let field_decls: Vec<RExpr> = model.fields.iter_mut().map(|f| f.decl.clone()).collect();
    let mut bodies: Vec<RExpr> = model.funcs.iter_mut().map(|f| std::mem::replace(&mut f.body, RExpr::Block(Vec::new()))).collect();
    let mut facts: Vec<RExpr> = model.facts.iter_mut().map(|f| std::mem::replace(&mut f.body, RExpr::Block(Vec::new()))).collect();
    let mut asserts: Vec<RExpr> = model.asserts.iter_mut().map(|f| std::mem::replace(&mut f.body, RExpr::Block(Vec::new()))).collect();
    let mut sfacts: Vec<RExpr> = model.sig_facts.iter_mut().map(|f| std::mem::replace(&mut f.1, RExpr::Block(Vec::new()))).collect();
    let mut cmds: Vec<RExpr> = model.commands.iter_mut().map(|c| std::mem::replace(&mut c.formula, RExpr::Block(Vec::new()))).collect();
    let mut decls = field_decls.clone();
    let result = {
        let m: &Model = model;
        let mut t = Typer { h: Hier { model: m }, env: Vec::new(), fields: HashMap::new(), rets: HashMap::new(), busy: Vec::new() };
        let fail = |name: String| {
            AlloyError::new(
                ErrorKind::Type,
                None,
                format!(
                    "Name cannot be resolved; possible incorrect function/predicate call; perhaps you used ( ) when you should have used [ ]

This cannot be a correct call to {name}."
                ),
            )
        };
        (|| -> Result<(), AlloyError> {
            for (fi, body) in bodies.iter_mut().enumerate() {
                t.env.clear();
                for (l, b) in &m.funcs[fi].params {
                    let ty = t.decl_type(b);
                    t.env.push((*l, ty));
                }
                t.walk(body, false).map_err(fail)?;
            }
            t.env.clear();
            for e in facts.iter_mut().chain(asserts.iter_mut()).chain(sfacts.iter_mut()).chain(cmds.iter_mut()) {
                t.walk(e, false).map_err(fail)?;
            }
            for (fi, d) in decls.iter_mut().enumerate() {
                t.env.clear();
                t.env.push((m.fields[fi].this_local, Some(t.h.sig_type(m.fields[fi].owner))));
                t.walk(d, false).map_err(fail)?;
            }
            Ok(())
        })()
    };
    for (f, b) in model.funcs.iter_mut().zip(bodies) {
        f.body = b;
    }
    for (f, b) in model.facts.iter_mut().zip(facts) {
        f.body = b;
    }
    for (f, b) in model.asserts.iter_mut().zip(asserts) {
        f.body = b;
    }
    for (f, b) in model.sig_facts.iter_mut().zip(sfacts) {
        f.1 = b;
    }
    for (c, b) in model.commands.iter_mut().zip(cmds) {
        c.formula = b;
    }
    for (f, d) in model.fields.iter_mut().zip(decls) {
        f.decl = d;
    }
    result
}
