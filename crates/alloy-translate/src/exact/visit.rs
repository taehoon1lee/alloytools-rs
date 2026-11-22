//! `TranslateAlloyToKodkod` visitor over the Rust sema IR (`RExpr`), mirroring the Java AST the parser and
//! typechecker produce (ExprList AND/OR are flattened by `addAND`/`addOR`, multiplicity markers on decl bounds,
//! `ExprQt.desugar` for `disj`, implicit casts via `toInt`/`toSet`).

use super::*;
use crate::resolve::Resolver;

/// `recursiveAddFormula` over the flattened command ExprList.
pub(super) fn flatten_top<'e>(e: &'e RExpr, out: &mut Vec<&'e RExpr>) {
    flatten_and(e, out)
}

/// A Java formula operand of an `ExprList` (`addAND`/`addOR` flattening).
fn flatten_and<'e>(e: &'e RExpr, out: &mut Vec<&'e RExpr>) {
    match e {
        RExpr::Block(items) => {
            for i in items {
                flatten_and(i, out);
            }
        }
        RExpr::Bin(BinOp::And, a, b) => {
            flatten_and(a, out);
            flatten_and(b, out);
        }
        x => out.push(x),
    }
}
fn flatten_or<'e>(e: &'e RExpr, out: &mut Vec<&'e RExpr>) {
    match e {
        RExpr::Bin(BinOp::Or, a, b) => {
            flatten_or(a, out);
            flatten_or(b, out);
        }
        x => out.push(x),
    }
}

/// Multiplicity marker of a decl bound (Java `Expr.mult()`), and the bound under it.
pub(super) fn decl_mult(e: &RExpr) -> (Option<UnOp>, &RExpr) {
    match e {
        RExpr::Un(op @ (UnOp::Set | UnOp::One | UnOp::Lone | UnOp::Some | UnOp::ExactlyOf), x) => {
            (Some(*op), x)
        }
        _ => (None, e),
    }
}

impl<'a> Cx<'a> {
    // ---------------------------------------------------------------- conversions (cform / cset / cint)

    pub(super) fn cform(&mut self, e: &RExpr) -> Result<N, AlloyError> {
        match self.visit(e)? {
            V::F(f) => Ok(f),
            other => Err(fatal(format!(
                "This should have been a formula: {other:?} from {:.300}",
                format!("{e:?}")
            ))),
        }
    }
    fn to_set(&mut self, v: V) -> Result<N, AlloyError> {
        match v {
            V::E(e) => Ok(e),
            V::I(i) => Ok(self.ast.add(Node::I2E(CastOp::IntCast, i))),
            V::F(_) => Err(fatal("This should have been a set or a relation.")),
        }
    }
    pub(super) fn cset(&mut self, e: &RExpr) -> Result<N, AlloyError> {
        let v = self.visit(e)?;
        self.to_set(v)
    }
    fn to_int(&mut self, v: V) -> Result<N, AlloyError> {
        match v {
            V::I(i) => {
                if let Node::E2I(_, x) = self.ast.get(i).clone() {
                    if let Node::I2E(_, ie) = self.ast.get(x).clone() {
                        return Ok(ie);
                    }
                }
                Ok(i)
            }
            V::E(e) => {
                if let Node::I2E(_, ie) = self.ast.get(e).clone() {
                    return Ok(ie);
                }
                Ok(self.ast.add(Node::E2I(CastOp::Sum, e)))
            }
            V::F(_) => Err(fatal("This should have been an integer expression.")),
        }
    }
    fn cint(&mut self, e: &RExpr) -> Result<N, AlloyError> {
        let v = self.visit(e)?;
        self.to_int(v)
    }
    /// `TranslateAlloyToKodkod.sum(Expression)`
    fn sum_of(&mut self, e: N) -> N {
        if let Node::I2E(_, ie) = self.ast.get(e).clone() {
            return ie;
        }
        self.ast.add(Node::E2I(CastOp::Sum, e))
    }
    fn iden(&mut self) -> N {
        // Expression.IDEN.intersection(a2k(UNIV).product(Expression.UNIV))
        let i = self.ast.iden();
        let u = self.univ;
        let uu = self.ast.univ();
        let p = self.ast.product(u, uu);
        self.ast.intersection(i, p)
    }
    fn iconst(&mut self, v: i32) -> N {
        self.ast.add(Node::IConst(v))
    }

    /// `TranslateAlloyToKodkod.skolem(name)`
    fn skolem_name(&self, name: &str) -> String {
        match self.current_function.last() {
            None => {
                let l = &self.cmd.name;
                if !l.is_empty() && !l.contains('$') {
                    format!("{l}_{name}")
                } else {
                    name.to_string()
                }
            }
            Some(&f) => {
                let label = &self.model.funcs[f as usize].label;
                let tail = label.rsplit('/').next().unwrap_or(label);
                if !tail.contains('$') {
                    format!("{tail}_{name}")
                } else {
                    name.to_string()
                }
            }
        }
    }

    fn env_get(&self, l: LocalId) -> Option<V> {
        self.env
            .iter()
            .rev()
            .find(|(x, _)| *x == l)
            .map(|(_, v)| *v)
    }

    /// `getSingleFormula`: heap-shaped binary tree of and/or over the (flattened) list.
    fn single_formula(&mut self, conj: bool, i: usize, fs: &[&RExpr]) -> Result<N, AlloyError> {
        let n = fs.len();
        if n == 0 {
            return Ok(if conj { self.ast.tru() } else { self.ast.fls() });
        }
        let mut me = self.cform(fs[i - 1])?;
        let c1 = i + i;
        let c2 = c1 + 1;
        if c1 > n {
            return Ok(me);
        }
        let other = self.single_formula(conj, c1, fs)?;
        me = self
            .ast
            .binf(me, if conj { FOp::And } else { FOp::Or }, other);
        if c2 > n {
            return Ok(me);
        }
        let other = self.single_formula(conj, c2, fs)?;
        me = self
            .ast
            .binf(me, if conj { FOp::And } else { FOp::Or }, other);
        Ok(me)
    }

    // ---------------------------------------------------------------- visit

    pub(super) fn visit(&mut self, e: &RExpr) -> Result<V, AlloyError> {
        Ok(match e {
            RExpr::Sig(s) => V::E(match *s {
                SIG_UNIV => self.univ,
                _ => self.a2k_sig[*s as usize]
                    .ok_or_else(|| fatal("Sig is not bound to a legal value during translation"))?,
            }),
            RExpr::Field(f) => V::E(
                self.a2k_field[*f as usize]
                    .ok_or_else(|| fatal("Field is not bound during translation"))?,
            ),
            RExpr::Local(l) if self.lazy.iter().any(|(x, _)| x == l) => {
                let x = self.lazy.iter().rev().find(|(x, _)| x == l).map(|(_, e)| e.clone()).expect("checked");
                self.visit(&x)?
            }
            RExpr::Local(l) => self.env_get(*l).ok_or_else(|| {
                fatal(format!(
                    "Variable \"{}\" is not bound to a legal value during translation.",
                    self.model.locals[*l as usize]
                ))
            })?,
            RExpr::Const(c) => match c {
                Const::Univ => V::E(self.univ),
                Const::Iden => V::E(self.iden()),
                Const::None => V::E(self.ast.none()),
                Const::SigInt => V::E(self.ast.ints()),
                Const::SigString => V::E(self.kk_string),
                Const::IntMin => V::I(self.iconst(self.min)),
                Const::IntMax => V::I(self.iconst(self.max)),
                Const::IntNext => V::E(self.kk_next),
                Const::This => return Err(unsupported("bare `this` constant")),
            },
            RExpr::Num(n) => {
                let c = self.iconst(*n);
                V::E(self.ast.add(Node::I2E(CastOp::IntCast, c)))
            }
            RExpr::Str(s) => V::E(
                *self
                    .s2k
                    .get(s)
                    .ok_or_else(|| fatal("String literal does not exist in this instance"))?,
            ),
            RExpr::Un(op, x) => self.visit_un(*op, x)?,
            RExpr::Bin(op, a, b) => self.visit_bin(*op, a, b)?,
            RExpr::Ite(c, a, b) => {
                let cf = self.cform(c)?;
                match self.visit(a)? {
                    V::F(l) => {
                        let c1 = self.ast.binf(cf, FOp::Implies, l);
                        let nc = self.ast.not(cf);
                        let r = self.cform(b)?;
                        let c2 = self.ast.binf(nc, FOp::Implies, r);
                        V::F(self.ast.binf(c1, FOp::And, c2))
                    }
                    V::E(l) => {
                        let r = self.cset(b)?;
                        V::E(self.ast.add(Node::IfE(cf, l, r)))
                    }
                    V::I(l) => {
                        let r = self.cint(b)?;
                        V::I(self.ast.add(Node::IfI(cf, l, r)))
                    }
                }
            }
            RExpr::Let(binds, body) => {
                let old = self.env.len();
                let oldt = self.ltypes.len();
                let oldl = self.lazy.len();
                for (l, x) in binds {
                    if self.model.macro_locals.contains(l) {
                        self.lazy.push((*l, x.clone()));
                    } else {
                        let v = self.visit(x)?;
                        self.env.push((*l, v));
                    }
                    self.bind_type(*l, x);
                }
                let r = self.visit(body)?;
                self.env.truncate(old);
                self.ltypes.truncate(oldt);
                self.lazy.truncate(oldl);
                r
            }
            RExpr::Call(fid, args) => self.visit_call(*fid, args)?,
            // a block with one element is that element (e.g. a fun body `{ e }`)
            RExpr::Block(items) if items.len() == 1 => self.visit(&items[0])?,
            RExpr::Block(_) => {
                let mut fs = Vec::new();
                flatten_and(e, &mut fs);
                V::F(self.single_formula(true, 1, &fs)?)
            }
            RExpr::Disj(args) => {
                let mut answer: Option<N> = None;
                let mut a: Option<N> = None;
                for arg in args {
                    let b = self.cset(arg)?;
                    match a {
                        None => {
                            a = Some(b);
                            continue;
                        }
                        Some(av) => {
                            let i = self.ast.intersection(av, b);
                            let no = self.ast.mult(Mult::No, i);
                            answer = Some(match answer {
                                None => no,
                                Some(x) => self.ast.binf(no, FOp::And, x),
                            });
                            a = Some(self.ast.union(av, b));
                        }
                    }
                }
                V::F(match answer {
                    Some(x) => x,
                    None => self.ast.tru(),
                })
            }
            RExpr::TotalOrder(args) => self.visit_total_order(args)?,
            RExpr::Quant(q, decls, body) => self.visit_qt_desugar(QtOp::from(*q), decls, body)?,
            RExpr::Compr(decls, body) => self.visit_qt_desugar(QtOp::Compr, decls, body)?,
            RExpr::Choice(c) if c.len() == 1 => self.visit(&c[0].clone())?,
            RExpr::Choice(_) => {
                let r = self.resolve(e, &crate::resolve::Exp::Any)?;
                if crate::resolve::is_choice(&r) {
                    return Err(unsupported(format!(
                        "overloaded name still ambiguous after type resolution: {:.700}",
                        format!("{r:?}")
                    )));
                }
                self.visit(&r)?
            }
        })
    }

    fn visit_un(&mut self, op: UnOp, x: &RExpr) -> Result<V, AlloyError> {
        Ok(match op {
            UnOp::Not => {
                let f = self.cform(x)?;
                V::F(self.ast.not(f))
            }
            UnOp::No | UnOp::Some | UnOp::Lone | UnOp::One => {
                let s = self.cset(x)?;
                let m = match op {
                    UnOp::No => Mult::No,
                    UnOp::Some => Mult::Some,
                    UnOp::Lone => Mult::Lone,
                    _ => Mult::One,
                };
                V::F(self.ast.mult(m, s))
            }
            UnOp::Set | UnOp::ExactlyOf => V::E(self.cset(x)?),
            UnOp::Seq => {
                let b = self.cset(x)?;
                V::E(self.ast.product(self.kk_seqidx, b))
            }
            UnOp::Card => {
                let s = self.cset(x)?;
                V::I(self.ast.add(Node::E2I(CastOp::Cardinality, s)))
            }
            UnOp::Transpose => {
                let s = self.cset(x)?;
                V::E(self.ast.transpose(s))
            }
            UnOp::Closure => {
                let s = self.cset(x)?;
                V::E(self.ast.closure(s))
            }
            UnOp::ReflClosure => {
                let iden = self.iden();
                let s = self.cset(x)?;
                let c = self.ast.closure(s);
                V::E(self.ast.union(c, iden))
            }
            UnOp::IntCast => {
                // CAST2SIGINT(CAST2INT(e)) = cint(CAST2INT e).toExpression()
                let s = self.cset(x)?;
                let i = self.sum_of(s);
                V::E(self.ast.add(Node::I2E(CastOp::IntCast, i)))
            }
            // CompModule.visit(ExprBadJoin): `Int[x]` with an integer-typed x is x itself
            UnOp::SigInt => self.visit(x)?,
            UnOp::Neg => {
                let i = self.cint(x)?;
                V::I(self.ast.add(Node::UnI(IOp::Neg, i)))
            }
            UnOp::Prime
            | UnOp::Always
            | UnOp::Eventually
            | UnOp::Historically
            | UnOp::Once
            | UnOp::Before
            | UnOp::After => return Err(unsupported("temporal operators in the exact pipeline")),
        })
    }

    fn icmp(&mut self, op: ICmpOp, a: &RExpr, b: &RExpr) -> Result<V, AlloyError> {
        let i = self.cint(a)?;
        let j = self.cint(b)?;
        Ok(V::F(self.ast.add(Node::ICmp(op, i, j))))
    }
    fn ibin(&mut self, op: IOp, a: &RExpr, b: &RExpr) -> Result<V, AlloyError> {
        let i = self.cint(a)?;
        let j = self.cint(b)?;
        Ok(V::I(self.ast.add(Node::BinI(op, i, j))))
    }

    fn visit_bin(&mut self, op: BinOp, a: &RExpr, b: &RExpr) -> Result<V, AlloyError> {
        // overloaded operands are resolved against each other first (as in the fast translator)
        let (ra, rb);
        let (a, b) = match op {
            BinOp::Join if crate::resolve::is_choice(a) || crate::resolve::is_choice(b) => {
                (ra, rb) = self.resolve_join(a, b)?;
                (&ra, &rb)
            }
            BinOp::Plus
            | BinOp::Minus
            | BinOp::Intersect
            | BinOp::Override
            | BinOp::Arrow(..)
            | BinOp::Equals
            | BinOp::In
                if crate::resolve::is_choice(a) || crate::resolve::is_choice(b) =>
            {
                (ra, rb) = self.resolve_pair(a, b)?;
                (&ra, &rb)
            }
            BinOp::DomainRestrict if crate::resolve::is_choice(b) => {
                (ra, rb) = self.resolve_restrict(a, b, true)?;
                (&ra, &rb)
            }
            BinOp::RangeRestrict if crate::resolve::is_choice(a) => {
                (ra, rb) = self.resolve_restrict(a, b, false)?;
                (&ra, &rb)
            }
            _ => (a, b),
        };
        Ok(match op {
            BinOp::And | BinOp::Or => {
                let whole = RExpr::Bin(op, Box::new(a.clone()), Box::new(b.clone()));
                let mut fs = Vec::new();
                if op == BinOp::And {
                    flatten_and(&whole, &mut fs);
                } else {
                    flatten_or(&whole, &mut fs);
                }
                V::F(self.single_formula(op == BinOp::And, 1, &fs)?)
            }
            BinOp::Implies | BinOp::Iff => {
                let f = self.cform(a)?;
                let g = self.cform(b)?;
                V::F(self.ast.binf(
                    f,
                    if op == BinOp::Implies {
                        FOp::Implies
                    } else {
                        FOp::Iff
                    },
                    g,
                ))
            }
            BinOp::In => {
                let s = self.cset(a)?;
                V::F(self.is_in(s, b)?)
            }
            BinOp::Lt => self.icmp(ICmpOp::Lt, a, b)?,
            BinOp::Le => self.icmp(ICmpOp::Lte, a, b)?,
            BinOp::Gt => self.icmp(ICmpOp::Gt, a, b)?,
            BinOp::Ge => self.icmp(ICmpOp::Gte, a, b)?,
            BinOp::Override => {
                let s = self.cset(a)?;
                let t = self.cset(b)?;
                V::E(self.ast.add(Node::BinE(EOp::Override, s, t)))
            }
            BinOp::Mul => self.ibin(IOp::Multiply, a, b)?,
            BinOp::Div => self.ibin(IOp::Divide, a, b)?,
            BinOp::Rem => self.ibin(IOp::Modulo, a, b)?,
            BinOp::Shl => self.ibin(IOp::Shl, a, b)?,
            BinOp::Shr => self.ibin(IOp::Shr, a, b)?,
            BinOp::Sha => self.ibin(IOp::Sha, a, b)?,
            BinOp::Plus => {
                let s = self.cset(a)?;
                let t = self.cset(b)?;
                V::E(self.ast.union(s, t))
            }
            BinOp::IntPlus => self.ibin(IOp::Plus, a, b)?,
            BinOp::IntMinus => self.ibin(IOp::Minus, a, b)?,
            BinOp::Minus => {
                if let (RExpr::Num(0), RExpr::Num(m)) = (a, b) {
                    if *m == self.max + 1 {
                        return Ok(V::I(self.iconst(self.min)));
                    }
                }
                let s = self.cset(a)?;
                let t = self.cset(b)?;
                V::E(self.ast.difference(s, t))
            }
            BinOp::Intersect => {
                let s = self.cset(a)?;
                let t = self.cset(b)?;
                V::E(self.ast.intersection(s, t))
            }
            BinOp::Arrow(..) => {
                let s = self.cset(a)?;
                let t = self.cset(b)?;
                V::E(self.ast.product(s, t))
            }
            BinOp::Join => {
                let s = self.cset(a)?;
                let s2 = self.cset(b)?;
                if let RExpr::Sig(sg) = a {
                    if self.is_one(*sg) {
                        if let Node::BinE(EOp::Product, l, r) = self.ast.get(s2).clone() {
                            if l == s {
                                return Ok(V::E(r));
                            }
                        }
                    }
                }
                V::E(self.ast.join(s, s2))
            }
            BinOp::Equals => {
                let va = self.visit(a)?;
                let vb = self.visit(b)?;
                let el = self.to_set(va)?;
                let er = self.to_set(vb)?;
                match (self.ast.get(el).clone(), self.ast.get(er).clone()) {
                    (Node::I2E(_, x), Node::I2E(_, y)) => {
                        V::F(self.ast.add(Node::ICmp(ICmpOp::Eq, x, y)))
                    }
                    _ => V::F(self.ast.eq(el, er)),
                }
            }
            // ExprBinary.Op.DOMAIN.make: `S <: f` with f declared in S is just f
            BinOp::DomainRestrict if matches!((a, b), (RExpr::Sig(s), RExpr::Field(f)) if self.model.fields[*f as usize].owner == *s) => {
                self.visit(b)?
            }
            BinOp::DomainRestrict => {
                let mut s = self.cset(a)?;
                let s2 = self.cset(b)?;
                let ar = self.ast.arity(s2);
                for _ in 1..ar {
                    let u = self.ast.univ();
                    s = self.ast.product(s, u);
                }
                V::E(self.ast.intersection(s, s2))
            }
            BinOp::RangeRestrict => {
                let s = self.cset(a)?;
                let mut s2 = self.cset(b)?;
                let ar = self.ast.arity(s);
                for _ in 1..ar {
                    let u = self.ast.univ();
                    s2 = self.ast.product(u, s2);
                }
                V::E(self.ast.intersection(s, s2))
            }
            BinOp::Until | BinOp::Releases | BinOp::Since | BinOp::Triggered => {
                return Err(unsupported("temporal operators in the exact pipeline"))
            }
        })
    }

    fn visit_call(&mut self, fid: FuncId, args: &[RExpr]) -> Result<V, AlloyError> {
        let func = &self.model.funcs[fid as usize];
        let n = func.params.len();
        if n == 0 {
            if let Some(v) = self.const_cache.get(&fid) {
                return Ok(*v);
            }
        }
        if self.current_function.contains(&fid) {
            return Err(AlloyError::new(
                ErrorKind::Syntax,
                None,
                format!("{} cannot call itself recursively!", func.label),
            ));
        }
        if args.len() != n {
            return Err(fatal("call arity mismatch"));
        }
        let params = func.params.clone();
        let mut newenv = Vec::with_capacity(n);
        let mut newtypes = Vec::with_capacity(n);
        for (i, (pl, pb)) in params.iter().enumerate() {
            let arg = if crate::resolve::is_choice(&args[i]) {
                let exp = self
                    .ty(pb)
                    .map_or(crate::resolve::Exp::Any, crate::resolve::Exp::Same);
                self.resolve(&args[i], &exp)?
            } else {
                args[i].clone()
            };
            let s = self.cset(&arg)?;
            newenv.push((*pl, V::E(s)));
            let t = self.ty(&arg).unwrap_or_else(|| {
                kodkod::instance::TupleSet::from_tuples(1, std::iter::empty::<Vec<u32>>())
            });
            newtypes.push((*pl, t));
        }
        let body = self.model.funcs[fid as usize].body.clone();
        let oldenv = std::mem::replace(&mut self.env, newenv);
        let oldtypes = std::mem::replace(&mut self.ltypes, newtypes);
        let oldlazy = std::mem::take(&mut self.lazy);
        self.current_function.push(fid);
        let ans = self.visit(&body);
        self.env = oldenv;
        self.ltypes = oldtypes;
        self.lazy = oldlazy;
        self.current_function.pop();
        let mut ans = ans?;
        // CompModule.resolveFuncBody: a fun body is `resolve_as_set`, so a small-int body becomes `Int[body]`
        if !self.model.funcs[fid as usize].is_pred && java_small_int(&body, &mut Vec::new()) {
            if let V::I(i) = ans {
                ans = V::E(self.ast.add(Node::I2E(CastOp::IntCast, i)));
            }
        }
        if n == 0 {
            self.const_cache.insert(fid, ans);
        }
        Ok(ans)
    }

    fn visit_total_order(&mut self, args: &[RExpr]) -> Result<V, AlloyError> {
        let elem = self.cset(&args[0])?;
        let first = self.cset(&args[1])?;
        let next = self.cset(&args[2])?;
        let is_rel = |c: &Self, x: N| matches!(c.ast.get(x), Node::Rel(_));
        if is_rel(self, elem) && is_rel(self, first) && is_rel(self, next) {
            let name = format!("{}_last", self.ast.rel_info(elem).name);
            let up = self.query(true, elem)?;
            let lst = self.add_rel(&name, None, up, 1, false);
            return Ok(V::F(self.ast.add(Node::PTotal(next, elem, first, lst))));
        }
        // every element is in the order; the first has no predecessor; each element but the first has one
        // predecessor, each but the last one successor; no cycles
        let rc = self.ast.add(Node::UnE(EOp::ReflexiveClosure, next));
        let fr = self.ast.join(first, rc);
        let f1 = self.ast.in_(elem, fr);
        let nf = self.ast.join(next, first);
        let f2 = self.ast.mult(Mult::No, nf);
        let e = self.ast.var(&format!("v{}", self.cnt), 1);
        self.cnt += 1;
        let ef = self.ast.eq(e, first);
        let ne = self.ast.join(next, e);
        let ne1 = self.ast.mult(Mult::One, ne);
        let f3 = self.ast.binf(ef, FOp::Or, ne1);
        let nel = self.ast.join(next, elem);
        let last = self.ast.difference(elem, nel);
        let el = self.ast.eq(e, last);
        let en = self.ast.join(e, next);
        let en1 = self.ast.mult(Mult::One, en);
        let f4 = self.ast.binf(el, FOp::Or, en1);
        let nc = self.ast.closure(next);
        let enc = self.ast.join(e, nc);
        let cyc = self.ast.in_(e, enc);
        let f5 = self.ast.not(cyc);
        let f34 = self.ast.binf(f3, FOp::And, f4);
        let f345 = self.ast.binf(f34, FOp::And, f5);
        let d = self.ast.one_of(e, elem);
        let all = self.ast.quantify(Quant::All, d, f345);
        let a1 = self.ast.binf(all, FOp::And, f1);
        Ok(V::F(self.ast.binf(a1, FOp::And, f2)))
    }

    // ---------------------------------------------------------------- isIn / isInBinary

    /// Java `right.mult != 0 && op.isArrow` for an arrow bound
    fn is_mult_arrow(e: &RExpr) -> bool {
        match e {
            RExpr::Bin(BinOp::Arrow(l, r), a, b) => {
                !(*l == AMult::Set && *r == AMult::Set)
                    || Self::is_mult_arrow(a)
                    || Self::is_mult_arrow(b)
            }
            RExpr::Un(UnOp::Seq, _) => true,
            _ => false,
        }
    }

    pub(super) fn is_in(&mut self, a: N, right: &RExpr) -> Result<N, AlloyError> {
        if Self::is_mult_arrow(right) {
            return self.is_in_binary(a, right);
        }
        let (m, inner) = decl_mult(right);
        let b = self.cset(inner)?;
        Ok(match m {
            Some(UnOp::ExactlyOf) => self.ast.eq(a, b),
            Some(UnOp::One) => {
                let o = self.ast.mult(Mult::One, a);
                let i = self.ast.in_(a, b);
                self.ast.binf(o, FOp::And, i)
            }
            Some(UnOp::Lone) => {
                let o = self.ast.mult(Mult::Lone, a);
                let i = self.ast.in_(a, b);
                self.ast.binf(o, FOp::And, i)
            }
            Some(UnOp::Some) => {
                let o = self.ast.mult(Mult::Some, a);
                let i = self.ast.in_(a, b);
                self.ast.binf(o, FOp::And, i)
            }
            _ => self.ast.in_(a, b),
        })
    }

    fn am(&mut self, a: N, d: Option<N>, v: N) -> N {
        let col = if self.ast.arity(a) == 1 {
            a
        } else {
            self.ast.univ()
        };
        let nd = self.ast.one_of(v, col);
        match d {
            None => nd,
            Some(x) => self.ast.decls_and(x, nd),
        }
    }

    fn is_in_binary(&mut self, r: N, ab: &RExpr) -> Result<N, AlloyError> {
        // `seq X` = ISSEQ_ARROW_LONE(seq/Int, X)
        let (lm, rm, left, right, isseq) = match ab {
            RExpr::Bin(BinOp::Arrow(l, rr), x, y) => {
                let (x, y) = self.resolve_pair(x, y)?;
                (*l, *rr, x, y, false)
            }
            RExpr::Un(UnOp::Seq, y) => (
                AMult::Set,
                AMult::Lone,
                RExpr::Sig(SIG_SEQINT),
                (**y).clone(),
                true,
            ),
            _ => unreachable!(),
        };
        let a = self.cset(&left)?;
        let b = self.cset(&right)?;
        let mut d: Option<N> = None;
        let mut atuple: Option<N> = None;
        let mut ar = r;
        let aar = self.ast.arity(a);
        for _ in 0..aar {
            let v = self.ast.var(&format!("v{}", self.cnt), 1);
            self.cnt += 1;
            d = Some(self.am(a, d, v));
            ar = self.ast.join(v, ar);
            atuple = Some(match atuple {
                None => v,
                Some(t) => self.ast.product(t, v),
            });
        }
        let mut ans1 = self.is_in(ar, &right)?;
        let rmult = match rm {
            AMult::Lone => Some(Mult::Lone),
            AMult::One => Some(Mult::One),
            AMult::Some => Some(Mult::Some),
            AMult::Set => None,
        };
        if let Some(m) = rmult {
            let mm = self.ast.mult(m, ar);
            ans1 = self.ast.binf(mm, FOp::And, ans1);
        }
        if aar > 1 {
            let tmp = self.is_in(atuple.unwrap(), &left)?;
            if !matches!(self.ast.get(tmp), Node::ConstF(true)) {
                ans1 = self.ast.binf(tmp, FOp::Implies, ans1);
            }
        }
        ans1 = self.ast.quantify(Quant::All, d.unwrap(), ans1);
        let mut d2: Option<N> = None;
        let mut btuple: Option<N> = None;
        let mut rb = r;
        let bar = self.ast.arity(b);
        for _ in 0..bar {
            let v = self.ast.var(&format!("v{}", self.cnt), 1);
            self.cnt += 1;
            d2 = Some(self.am(b, d2, v));
            rb = self.ast.join(rb, v);
            btuple = Some(match btuple {
                None => v,
                Some(t) => self.ast.product(v, t),
            });
        }
        let mut ans2 = self.is_in(rb, &left)?;
        let lmult = match lm {
            AMult::Lone => Some(Mult::Lone),
            AMult::One => Some(Mult::One),
            AMult::Some => Some(Mult::Some),
            AMult::Set => None,
        };
        if let Some(m) = lmult {
            let mm = self.ast.mult(m, rb);
            ans2 = self.ast.binf(mm, FOp::And, ans2);
        }
        if bar > 1 {
            let tmp = self.is_in(btuple.unwrap(), &right)?;
            if !matches!(self.ast.get(tmp), Node::ConstF(true)) {
                ans2 = self.ast.binf(tmp, FOp::Implies, ans2);
            }
        }
        ans2 = self.ast.quantify(Quant::All, d2.unwrap(), ans2);
        let prod = self.ast.product(a, b);
        let inr = self.ast.in_(r, prod);
        let x = self.ast.binf(inr, FOp::And, ans1);
        let mut ans = self.ast.binf(x, FOp::And, ans2);
        if isseq {
            let mut rr = r;
            while self.ast.arity(rr) > 1 {
                let u = self.ast.univ();
                rr = self.ast.join(rr, u);
            }
            let rj = self.ast.join(rr, self.kk_next);
            let diff = self.ast.difference(rr, rj);
            let z = self.ast.in_(diff, self.kk_zero);
            ans = self.ast.binf(z, FOp::And, ans);
        }
        Ok(ans)
    }

    // ---------------------------------------------------------------- quantifiers (ExprQt)

    /// `ExprQt.desugar()` + `visit_qt`
    fn visit_qt_desugar(
        &mut self,
        op: QtOp,
        decls: &[RDecl],
        body: &RExpr,
    ) -> Result<V, AlloyError> {
        let has_disj = decls.iter().any(|d| d.disjoint && d.vars.len() > 1);
        if !has_disj {
            return self.visit_qt(op, decls, body);
        }
        // guard = disj_k and ... and disj_1 (each makeDISJOINT.and(guard), flattened)
        let mut guard: Vec<RExpr> = Vec::new();
        let mut newdecls = Vec::new();
        for d in decls {
            if d.vars.len() <= 1 || !d.disjoint {
                newdecls.push(d.clone());
                continue;
            }
            let dj = RExpr::Disj(d.vars.iter().map(|l| RExpr::Local(*l)).collect());
            let mut g = vec![dj];
            g.extend(guard);
            guard = g;
            newdecls.push(RDecl {
                vars: d.vars.clone(),
                disjoint: false,
                bound: d.bound.clone(),
            });
        }
        let g = if guard.len() == 1 {
            guard.pop().unwrap()
        } else {
            RExpr::Block(guard)
        };
        let sub = match op {
            QtOp::Sum => return Err(unsupported("sum over disj decls")),
            QtOp::All => RExpr::Bin(BinOp::Implies, Box::new(g), Box::new(body.clone())),
            _ => RExpr::Block(vec![g, body.clone()]),
        };
        self.visit_qt(op, &newdecls, &sub)
    }

    /// `addOne(decl expr)` + its multiplicity
    fn add_one<'e>(&mut self, e: &'e RExpr) -> Result<(Option<UnOp>, &'e RExpr), AlloyError> {
        let (m, inner) = decl_mult(e);
        if m.is_some() {
            return Ok((m, inner));
        }
        Ok((None, e))
    }

    fn visit_qt(&mut self, op: QtOp, decls: &[RDecl], body: &RExpr) -> Result<V, AlloyError> {
        if op == QtOp::No {
            let nb = RExpr::Un(UnOp::Not, Box::new(body.clone()));
            return self.visit_qt(QtOp::All, decls, &nb);
        }
        if op == QtOp::One || op == QtOp::Lone {
            let mut ok = true;
            for d in decls {
                let (m, inner) = decl_mult(&d.bound);
                let unary = self.static_arity(inner)? == 1;
                // addOne: a unary bound without multiplicity becomes ONEOF
                let eff = if m.is_none() && unary {
                    Some(UnOp::One)
                } else {
                    m
                };
                if !unary || eff != Some(UnOp::One) {
                    ok = false;
                    break;
                }
            }
            if ok {
                let c = match self.visit_qt(QtOp::Compr, decls, body)? {
                    V::E(c) => c,
                    _ => unreachable!(),
                };
                return Ok(V::F(self.ast.mult(
                    if op == QtOp::One {
                        Mult::One
                    } else {
                        Mult::Lone
                    },
                    c,
                )));
            }
            if op == QtOp::One {
                let f1 = match self.visit_qt(QtOp::Lone, decls, body)? {
                    V::F(f) => f,
                    _ => unreachable!(),
                };
                let f2 = match self.visit_qt(QtOp::Some, decls, body)? {
                    V::F(f) => f,
                    _ => unreachable!(),
                };
                return Ok(V::F(self.ast.binf(f1, FOp::And, f2)));
            }
            return Err(unsupported(
                "lone quantifier over non-unary decls in the exact pipeline",
            ));
        }
        let mut dd: Option<N> = None;
        let mut guards: Vec<N> = Vec::new();
        let old = self.env.len();
        let oldt = self.ltypes.len();
        for d in decls {
            let (m, inner) = decl_mult(&d.bound);
            let inner_r;
            let inner = if crate::resolve::is_choice(inner) {
                inner_r = self.resolve(inner, &crate::resolve::Exp::Any)?;
                &inner_r
            } else {
                inner
            };
            let dv = self.cset(inner)?;
            let arity = self.ast.arity(dv);
            for &l in &d.vars {
                let name = self.skolem_name(&self.model.locals[l as usize].clone());
                let v = self.ast.var(&name, arity);
                // A4Solution.kv2typepos: only these variables have an Alloy type (skolems of others are not shown)
                self.typed_vars.insert(v);
                self.env.push((l, V::E(v)));
                self.bind_type(l, inner);
                let newd = if arity != 1 {
                    let g = self.is_in(v, &d.bound)?;
                    guards.push(g);
                    self.ast.declare(v, Mult::Set, dv)
                } else {
                    let mm = match m {
                        Some(UnOp::Set) => Mult::Set,
                        Some(UnOp::Some) => Mult::Some,
                        Some(UnOp::Lone) => Mult::Lone,
                        _ => Mult::One,
                    };
                    self.ast.declare(v, mm, dv)
                };
                dd = Some(match dd {
                    None => newd,
                    Some(x) => self.ast.decls_and(x, newd),
                });
            }
        }
        let dd = dd.ok_or_else(|| fatal("quantifier without decls"))?;
        let res = if op == QtOp::Sum {
            let i = self.cint(body)?;
            self.env.truncate(old);
            self.ltypes.truncate(oldt);
            V::I(self.ast.add(Node::Sum(dd, i)))
        } else {
            let f = self.cform(body)?;
            self.env.truncate(old);
            self.ltypes.truncate(oldt);
            match op {
                QtOp::Compr => V::E(self.ast.comprehension(dd, f)),
                QtOp::Some => {
                    if guards.is_empty() {
                        V::F(self.ast.quantify(Quant::Some, dd, f))
                    } else {
                        guards.push(f);
                        let g = self.ast.and_all(&guards);
                        V::F(self.ast.quantify(Quant::Some, dd, g))
                    }
                }
                _ => {
                    if guards.is_empty() {
                        V::F(self.ast.quantify(Quant::All, dd, f))
                    } else {
                        let g = self.ast.and_all(&guards);
                        let imp = self.ast.binf(g, FOp::Implies, f);
                        V::F(self.ast.quantify(Quant::All, dd, imp))
                    }
                }
            }
        };
        Ok(res)
    }

    /// Arity of an Alloy expression without translating it (types are sets of sig products).
    fn static_arity(&mut self, e: &RExpr) -> Result<u32, AlloyError> {
        let mut tenv: Vec<(LocalId, JType)> = Vec::new();
        for (l, v) in self.env.clone() {
            if let V::E(n) = v {
                let ar = self.ast.arity(n) as usize;
                tenv.push((
                    l,
                    JType {
                        entries: vec![vec![SIG_UNIV; ar]],
                    },
                ));
            }
        }
        match self.expr_type(e, &mut tenv) {
            Ok(t) => Ok(t.entries.first().map(|x| x.len()).unwrap_or(1) as u32),
            Err(_) => {
                // fall back to translating a throwaway copy
                let mark = self.ast.nodes.len();
                let cnt = self.cnt;
                let r = self.cset(e).map(|n| self.ast.arity(n));
                self.ast.nodes.truncate(mark);
                self.cnt = cnt;
                r
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum QtOp {
    All,
    Some,
    No,
    Lone,
    One,
    Sum,
    Compr,
}

impl From<AQuant> for QtOp {
    fn from(q: AQuant) -> Self {
        match q {
            AQuant::All => QtOp::All,
            AQuant::Some => QtOp::Some,
            AQuant::No => QtOp::No,
            AQuant::Lone => QtOp::Lone,
            AQuant::One => QtOp::One,
            AQuant::Sum => QtOp::Sum,
        }
    }
}

/// Java `Type.is_small_int()` of an expression (`Type.smallIntType()`): numbers, `#`, integer arithmetic, `sum`,
/// and lets / `Int[..]` of those. `small` holds the let-bound locals that are small ints.
fn java_small_int(e: &RExpr, small: &mut Vec<LocalId>) -> bool {
    match e {
        RExpr::Num(_) => true,
        RExpr::Un(UnOp::Card | UnOp::Neg, _) => true,
        RExpr::Un(UnOp::SigInt, x) => java_small_int(x, small),
        RExpr::Bin(BinOp::IntPlus | BinOp::IntMinus | BinOp::Mul | BinOp::Div | BinOp::Rem | BinOp::Shl | BinOp::Shr | BinOp::Sha, ..) => true,
        RExpr::Quant(AQuant::Sum, ..) => true,
        RExpr::Block(v) if v.len() == 1 => java_small_int(&v[0], small),
        RExpr::Local(l) => small.contains(l),
        RExpr::Let(binds, b) => {
            let old = small.len();
            for (l, x) in binds {
                if java_small_int(x, small) {
                    small.push(*l);
                }
            }
            let r = java_small_int(b, small);
            small.truncate(old);
            r
        }
        _ => false,
    }
}
