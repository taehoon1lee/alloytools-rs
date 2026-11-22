//! Universe/int/string setup (A4Solution constructor, ScopeComputer atoms) and `BoundsComputer`.

use super::*;

impl<'a> Cx<'a> {
    pub fn new(
        model: &'a Model,
        cmd: &'a RCommand,
        labels: Vec<String>,
    ) -> Result<Cx<'a>, AlloyError> {
        let lay = compute_scopes(model, cmd)?;
        let bitwidth = cmd.bitwidth.unwrap_or(4);
        if !(0..=30).contains(&bitwidth) {
            return Err(unsupported("bitwidth out of range"));
        }
        let (min, max) = if bitwidth < 1 {
            (0, -1)
        } else {
            (-(1i32 << (bitwidth - 1)), (1i32 << (bitwidth - 1)) - 1)
        };
        // ScopeComputer: maxseq defaults to the overall scope (or 4), at most max
        let mut maxseq = match cmd.maxseq {
            Some(m) if m >= 0 => m,
            _ => {
                let m = cmd.overall.filter(|o| *o >= 0).unwrap_or(4);
                m.min(max)
            }
        };
        if maxseq > max {
            return Err(AlloyError::new(
                ErrorKind::Syntax,
                None,
                format!("With integer bitwidth of {bitwidth}, you cannot have sequence length longer than {max}"),
            ));
        }
        if maxseq < 0 {
            maxseq = 0;
        }
        let (s0, s1) = lay.string_range;
        // sig atoms named Java's way: UniqueNameGenerator over the label without `this/`
        let mut atoms: Vec<String> = Vec::with_capacity(s0 as usize);
        let mut used: std::collections::HashSet<String> = std::collections::HashSet::new();
        let mut k = 0usize;
        while k < s0 as usize {
            let owner = lay.atom_sig[k];
            let mut end = k;
            while end < s0 as usize && lay.atom_sig[end] == owner {
                end += 1;
            }
            let l = &labels[owner as usize];
            let mut base = l.strip_prefix("this/").unwrap_or(l).to_string();
            while !used.insert(base.clone()) {
                base.push('\'');
            }
            for i in 0..(end - k) {
                atoms.push(format!("{base}${i}"));
            }
            k = end;
        }
        let int_atom0 = atoms.len() as u32;
        if max >= min {
            for i in min..=max {
                atoms.push(i.to_string());
            }
        }
        let str_atoms: Vec<String> = lay.atoms[s0 as usize..s1 as usize].to_vec();
        let str0 = atoms.len() as u32;
        atoms.extend(str_atoms.iter().cloned());
        if atoms.is_empty() {
            atoms.push("<empty>".into());
        }
        let mut ast = Ast::new();
        let mut bounds = Bounds {
            atoms,
            ..Default::default()
        };
        let mut sigint = Vec::new();
        let mut seqidx = Vec::new();
        let mut next = Vec::new();
        let n = bounds.universe_size();
        let kk_min = ast.rel("Int/min", 1);
        let kk_max = ast.rel("Int/max", 1);
        let kk_zero = ast.rel("Int/zero", 1);
        let kk_next = ast.rel("Int/next", 2);
        let kk_seqidx = ast.rel("seq/Int", 1);
        let kk_string = ast.rel("String", 1);
        if max >= min {
            for i in min..=max {
                let a = int_atom0 + (i - min) as u32;
                bounds.ints.insert(i, ts(1, vec![a]));
                sigint.push(a);
                if i >= 0 && i < maxseq {
                    seqidx.push(a);
                }
                if i < max {
                    next.push(a * n + a + 1);
                }
                if i == min {
                    bounds.bound_exactly(kk_min, ts(1, vec![a]));
                }
                if i == max {
                    bounds.bound_exactly(kk_max, ts(1, vec![a]));
                }
                if i == 0 {
                    bounds.bound_exactly(kk_zero, ts(1, vec![a]));
                }
            }
        }
        bounds.bound_exactly(kk_next, ts(2, next));
        bounds.bound_exactly(kk_seqidx, ts(1, seqidx.clone()));
        let mut s2k = HashMap::new();
        let mut strings = Vec::new();
        for (k, s) in str_atoms.iter().enumerate() {
            let a = str0 + k as u32;
            let lit = s.trim_matches('"').to_string();
            if model.strings.contains(&lit) {
                let r = ast.rel("", 1);
                bounds.bound_exactly(r, ts(1, vec![a]));
                s2k.insert(lit, r);
            }
            strings.push(a);
        }
        bounds.bound_exactly(kk_string, ts(1, strings.clone()));
        let ints = ast.ints();
        let univ = ast.union(ints, kk_string);
        let nsigs = model.sigs.len();
        let mut a2k_sig = vec![None; nsigs];
        a2k_sig[SIG_INT as usize] = Some(ints);
        a2k_sig[SIG_SEQINT as usize] = Some(kk_seqidx);
        a2k_sig[SIG_STRING as usize] = Some(kk_string);
        a2k_sig[SIG_NONE as usize] = Some(ast.none());
        let sigs: Vec<SigId> = (0..nsigs as SigId)
            .filter(|&s| model.sigs[s as usize].kind == SigKind::User)
            .collect();
        Ok(Cx {
            model,
            cmd,
            labels,
            ast,
            bounds,
            formulas: Vec::new(),
            a2k_sig,
            a2k_field: vec![None; model.fields.len()],
            univ,
            kk_next,
            kk_zero,
            kk_seqidx,
            kk_string,
            s2k,
            lay,
            int_atom0,
            min,
            max,
            bitwidth,
            sigint,
            seqidx,
            strings,
            cnt: 0,
            env: Vec::new(),
            current_function: Vec::new(),
            const_cache: HashMap::new(),
            ftypes: HashMap::new(),
            var_types: HashMap::new(),
            sigs,
            alloc_order: Vec::new(),
            ltypes: Vec::new(),
            ty_memo: vec![None; model.fields.len()],
            ub: HashMap::new(),
            lb: HashMap::new(),
        })
    }

    pub(super) fn scope_of(&self, s: SigId) -> i32 {
        self.lay.scope[s as usize].unwrap_or(-1)
    }
    pub(super) fn is_exact(&self, s: SigId) -> bool {
        self.lay.exact[s as usize]
    }
    fn prim_children(&self, s: SigId) -> Vec<SigId> {
        self.hier().children(s)
    }

    // BoundsComputer.computeLowerBound (atoms are consumed in universe order)
    fn compute_lower(&mut self, next_atom: &mut u32, s: SigId) -> Vec<u32> {
        let mut n = self.scope_of(s);
        let mut lower: Vec<u32> = Vec::new();
        for c in self.prim_children(s) {
            let l = self.compute_lower(next_atom, c);
            lower.extend(l);
        }
        lower.sort_unstable();
        let mut upper = lower.clone();
        let exact = self.is_exact(s);
        if exact || self.is_top(s) {
            n -= upper.len() as i32;
            while n > 0 {
                let a = *next_atom;
                *next_atom += 1;
                if exact {
                    lower.push(a);
                }
                upper.push(a);
                n -= 1;
            }
        }
        lower.sort_unstable();
        upper.sort_unstable();
        self.lb.insert(s, lower.clone());
        self.ub.insert(s, upper);
        lower
    }

    fn compute_upper(&mut self, s: SigId) {
        let mut x = self.ub[&s].clone();
        let ch = self.prim_children(s);
        for &c in &ch {
            let l = &self.lb[&c];
            x.retain(|a| !l.contains(a));
        }
        for c in ch {
            if self.scope_of(c) > self.lb[&c].len() as i32 {
                let u = self.ub.get_mut(&c).unwrap();
                u.extend(x.iter().copied());
                u.sort_unstable();
                u.dedup();
            }
            self.compute_upper(c);
        }
    }

    fn allocate_prim(&mut self, s: SigId) -> Result<N, AlloyError> {
        if self.model.sigs[s as usize].is_var {
            return Err(unsupported(
                "var sigs are not supported by the exact pipeline yet",
            ));
        }
        let mut sum: Option<N> = None;
        for c in self.prim_children(s) {
            let ce = self.allocate_prim(c)?;
            match sum {
                None => sum = Some(ce),
                Some(sm) => {
                    let i = self.ast.intersection(sm, ce);
                    let no = self.ast.mult(Mult::No, i);
                    self.add_formula(no);
                    sum = Some(self.ast.union(sm, ce));
                }
            }
        }
        let mut lower = self.lb[&s].clone();
        let mut upper = self.ub[&s].clone();
        let label = self.label(s).to_string();
        let e = match sum {
            None => self.add_rel(&label, Some(lower), upper, 1, false),
            Some(sm) if self.model.sigs[s as usize].is_abstract => sm,
            Some(sm) => {
                for c in self.prim_children(s) {
                    let ce = self.a2k(c);
                    let cts = self.query(false, ce)?;
                    lower.retain(|a| !cts.contains(a));
                    upper.retain(|a| !cts.contains(a));
                }
                let rem = self.add_rel(&format!("{label}_remainder"), Some(lower), upper, 1, false);
                self.ast.union(sm, rem)
            }
        };
        self.add_sig(s, e);
        Ok(e)
    }

    fn allocate_subset(&mut self, s: SigId) -> Result<N, AlloyError> {
        if let Some(e) = self.a2k_sig[s as usize] {
            if !matches!(self.ast.get(e), Node::ConstE(ConstE::None)) {
                return Ok(e);
            }
        }
        let parents = self.model.sigs[s as usize].subset_of.clone();
        let mut sum: Option<N> = None;
        let mut tsv: Vec<u32> = Vec::new();
        for p in parents {
            let pe = if self.is_prim(p) {
                self.a2k(p)
            } else {
                self.allocate_subset(p)?
            };
            tsv.extend(self.query(true, pe)?);
            sum = Some(match sum {
                None => pe,
                Some(x) => self.ast.union(x, pe),
            });
        }
        let sum = sum.ok_or_else(|| fatal("subset sig without parents"))?;
        if self.model.sigs[s as usize].is_exact {
            self.add_sig(s, sum);
            return Ok(sum);
        }
        tsv.sort_unstable();
        tsv.dedup();
        let label = self.label(s).to_string();
        let r = self.add_rel(&label, None, tsv, 1, self.model.sigs[s as usize].is_var);
        self.add_sig(s, r);
        let f = self.ast.in_(r, sum);
        self.add_formula(f);
        Ok(r)
    }

    /// `Sig.type()` (a subset sig has the union of its parents' types)
    pub(super) fn sig_type(&self, s: SigId) -> JType {
        let h = self.hier();
        if self.is_prim(s) {
            return h.make(s);
        }
        let mut t: Option<JType> = None;
        for &p in &self.model.sigs[s as usize].subset_of {
            let pt = self.sig_type(p);
            t = Some(match t {
                None => pt,
                Some(x) => {
                    let mut ee = x.entries.clone();
                    for e in pt.entries {
                        h.add(&mut ee, e);
                    }
                    JType { entries: ee }
                }
            });
        }
        t.unwrap_or_default()
    }

    /// `Field.type()`: owner type -> declared bound type
    pub(super) fn field_type(&mut self, f: FieldId) -> Result<JType, AlloyError> {
        if let Some(t) = self.ftypes.get(&f) {
            return Ok(t.clone());
        }
        let fd = &self.model.fields[f as usize];
        let owner = fd.owner;
        let decl = fd.decl.clone();
        let this_l = fd.this_local;
        let ot = self.sig_type(owner);
        let mut tenv = vec![(this_l, ot.clone())];
        let dt = self.expr_type(&decl, &mut tenv)?;
        let t = self.hier().product(&ot, &dt);
        self.ftypes.insert(f, t.clone());
        Ok(t)
    }

    /// Java static type of a (field-bound) expression.
    pub(super) fn expr_type(
        &mut self,
        e: &RExpr,
        tenv: &mut Vec<(LocalId, JType)>,
    ) -> Result<JType, AlloyError> {
        let h = self.hier();
        Ok(match e {
            RExpr::Sig(s) => self.sig_type(*s),
            RExpr::Field(f) => self.field_type(*f)?,
            RExpr::Local(l) => tenv
                .iter()
                .rev()
                .find(|(x, _)| x == l)
                .map(|(_, t)| t.clone())
                .ok_or_else(|| unsupported("type of an unbound local"))?,
            RExpr::Const(Const::Univ) => h.make(SIG_UNIV),
            RExpr::Const(Const::None) => h.make(SIG_NONE),
            RExpr::Const(Const::SigInt) | RExpr::Num(_) => h.make(SIG_INT),
            RExpr::Const(Const::SigString) | RExpr::Str(_) => h.make(SIG_STRING),
            RExpr::Const(Const::Iden) => h.product(&h.make(SIG_UNIV), &h.make(SIG_UNIV)),
            RExpr::Un(UnOp::Set | UnOp::One | UnOp::Lone | UnOp::Some | UnOp::ExactlyOf, x) => {
                self.expr_type(x, tenv)?
            }
            RExpr::Un(UnOp::Seq, x) => {
                let t = self.expr_type(x, tenv)?;
                h.product(&h.make(SIG_SEQINT), &t)
            }
            RExpr::Un(UnOp::Transpose, x) => {
                let t = self.expr_type(x, tenv)?;
                h.transpose(&t)
            }
            RExpr::Un(UnOp::Closure, x) => {
                let t = self.expr_type(x, tenv)?;
                h.closure(&t)
            }
            RExpr::Un(UnOp::IntCast | UnOp::SigInt | UnOp::Card, _) => h.make(SIG_INT),
            RExpr::Bin(BinOp::Arrow(..), a, b) => {
                let (x, y) = (self.expr_type(a, tenv)?, self.expr_type(b, tenv)?);
                h.product(&x, &y)
            }
            RExpr::Bin(BinOp::Plus | BinOp::Override, a, b) => {
                let (x, y) = (self.expr_type(a, tenv)?, self.expr_type(b, tenv)?);
                h.union(&x, &y)
            }
            RExpr::Bin(BinOp::Intersect, a, b) => {
                let (x, y) = (self.expr_type(a, tenv)?, self.expr_type(b, tenv)?);
                h.intersect(&x, &y)
            }
            RExpr::Bin(BinOp::Minus, a, _) => self.expr_type(a, tenv)?,
            RExpr::Bin(BinOp::Join, a, b) => {
                let (x, y) = (self.expr_type(a, tenv)?, self.expr_type(b, tenv)?);
                h.join(&x, &y)
            }
            RExpr::Block(items) if items.len() == 1 => self.expr_type(&items[0], tenv)?,
            _ => {
                return Err(unsupported(format!(
                    "Java type of field bound {:.80}",
                    format!("{e:?}")
                )))
            }
        })
    }

    /// The BoundsComputer constructor.
    pub(super) fn compute_bounds(&mut self) -> Result<(), AlloyError> {
        let mut next_atom = 0u32;
        let sigs = self.sigs.clone();
        for &s in &sigs {
            if self.is_top(s) {
                self.compute_lower(&mut next_atom, s);
            }
        }
        for &s in &sigs {
            if self.is_top(s) {
                self.compute_upper(s);
            }
        }
        for &s in &sigs {
            if self.is_top(s) {
                self.allocate_prim(s)?;
            }
        }
        for &s in &sigs {
            if !self.is_prim(s) {
                self.allocate_subset(s)?;
            }
        }
        for &s in &sigs {
            let fields = self.model.sigs[s as usize].fields.clone();
            let one = self.is_one(s);
            if one && fields.len() == 2 && self.is_enum_order(s) {
                return Err(unsupported(
                    "ordering over an enum (BoundsComputer special case)",
                ));
            }
            for f in fields {
                let fd = self.model.fields[f as usize].clone();
                if fd.is_var {
                    return Err(unsupported(
                        "var fields are not supported by the exact pipeline yet",
                    ));
                }
                if one && fd.defined {
                    if let Some(sim) = self.sim(&fd.decl) {
                        let se = self.a2k(s);
                        let p = self.ast.product(se, sim);
                        self.a2k_field[f as usize] = Some(p);
                        continue;
                    }
                }
                let ft = self.field_type(f)?;
                let h = self.hier();
                let t = if one {
                    h.join(&h.make(SIG_UNIV), &ft)
                } else {
                    ft
                };
                let arity = t.entries.first().map(|e| e.len()).unwrap_or(1) as u32;
                let usz = self.bounds.universe_size();
                let mut ub: Vec<u32> = Vec::new();
                for p in h.fold(&t) {
                    let mut up: Option<Vec<u32>> = None;
                    for b in p {
                        let be = self.a2k(b);
                        let tmp = self.query(true, be)?;
                        up = Some(match up {
                            None => tmp,
                            Some(x) => {
                                let mut v = Vec::with_capacity(x.len() * tmp.len());
                                for &a in &x {
                                    for &c in &tmp {
                                        v.push(a * usz + c);
                                    }
                                }
                                v
                            }
                        });
                    }
                    ub.extend(up.unwrap_or_default());
                }
                ub.sort_unstable();
                ub.dedup();
                let label = format!("{}.{}", self.label(s), fd.name);
                let r = self.add_rel(&label, None, ub, arity, false);
                let fe = if one {
                    let se = self.a2k(s);
                    self.ast.product(se, r)
                } else {
                    r
                };
                self.a2k_field[f as usize] = Some(fe);
            }
        }
        // symbolic bounds (Version.experimental)
        for &s in &sigs {
            self.symbolic_sig(s)?;
            for f in self.model.sigs[s as usize].fields.clone() {
                self.symbolic_field(f)?;
            }
        }
        // size constraints
        for &s in &sigs {
            let exp = self.a2k(s);
            let upper = self.query(true, exp)?.len();
            let lower = self.query(false, exp)?.len();
            let n = if self.is_prim(s) {
                self.scope_of(s)
            } else {
                -1
            };
            let sm = self.model.sigs[s as usize].mult;
            if sm == Some(AMult::One) {
                if lower != 1 || upper != 1 {
                    let f = self.ast.mult(Mult::One, exp);
                    self.add_formula(f);
                }
                continue;
            }
            if sm == Some(AMult::Some) && lower < 1 {
                let f = self.ast.mult(Mult::Some, exp);
                self.add_formula(f);
            }
            if sm == Some(AMult::Lone) && upper > 1 {
                let f = self.ast.mult(Mult::Lone, exp);
                self.add_formula(f);
            }
            if n < 0 {
                continue;
            }
            let exact = self.is_exact(s);
            if lower == n as usize && upper == n as usize && exact {
                // exact by its bounds
            } else if exact {
                let f = self.size(s, n, true);
                self.add_formula(f);
            } else if upper <= n as usize {
                // the bounds are tight enough
            } else {
                let f = self.size(s, n, false);
                self.add_formula(f);
            }
        }
        Ok(())
    }

    fn is_enum_order(&self, s: SigId) -> bool {
        self.model.sig_facts.iter().any(|(x, f)| {
            *x == s && matches!(f, RExpr::TotalOrder(a) if matches!(a.first(), Some(RExpr::Sig(e)) if self.model.sigs[*e as usize].is_enum))
        })
    }

    /// `BoundsComputer.sim(expr)`
    fn sim(&mut self, e: &RExpr) -> Option<N> {
        match e {
            RExpr::Un(UnOp::ExactlyOf, x) => self.sim(x),
            RExpr::Bin(
                op @ (BinOp::Arrow(AMult::Set, AMult::Set) | BinOp::Plus | BinOp::Join),
                a,
                b,
            ) => {
                let l = self.sim(a)?;
                let r = self.sim(b)?;
                Some(match op {
                    BinOp::Plus => self.ast.union(l, r),
                    BinOp::Join => self.ast.join(l, r),
                    _ => self.ast.product(l, r),
                })
            }
            RExpr::Const(Const::None) | RExpr::Sig(SIG_NONE) => Some(self.ast.none()),
            RExpr::Sig(SIG_INT) => Some(self.ast.ints()),
            RExpr::Sig(SIG_UNIV) => Some(self.univ),
            RExpr::Sig(s) => self.a2k_sig[*s as usize],
            RExpr::Field(f) => self.a2k_field[*f as usize],
            _ => None,
        }
    }

    /// `A4Solution.addSymbolicBound(Sig)`: only subset sigs
    fn symbolic_sig(&mut self, s: SigId) -> Result<(), AlloyError> {
        if self.is_prim(s) || self.is_top(s) {
            return Ok(());
        }
        let r = match self.a2k_sig[s as usize] {
            Some(e) if matches!(self.ast.get(e), Node::Rel(_)) => e,
            _ => return Ok(()),
        };
        if self.bounds.lower[&r].len() == self.bounds.upper[&r].len() {
            return Ok(());
        }
        let mut ke = self.ast.none();
        let parents = self.model.sigs[s as usize].subset_of.clone();
        for p in parents {
            let pe = self.a2k(p);
            ke = self.ast.union(ke, pe);
        }
        if !matches!(self.ast.get(ke), Node::ConstE(ConstE::None)) {
            self.bounds.remove_concrete(r);
            let lo = self.ast.none();
            self.bounds.symb.push((r, lo, ke));
        }
        Ok(())
    }

    /// `A4Solution.addSymbolicBound(Field)`
    fn symbolic_field(&mut self, f: FieldId) -> Result<(), AlloyError> {
        let e = match self.a2k_field[f as usize] {
            Some(e) => e,
            None => return Ok(()),
        };
        let r = match self.ast.get(e).clone() {
            Node::Rel(_) => e,
            Node::BinE(EOp::Product, _, r) if matches!(self.ast.get(r), Node::Rel(_)) => r,
            _ => {
                return Err(unsupported(
                    "symbolic bound of a field defined by an expression",
                ))
            }
        };
        if self.bounds.lower[&r].len() == self.bounds.upper[&r].len() {
            return Ok(());
        }
        let owner = self.model.fields[f as usize].owner;
        let one = self.is_one(owner);
        let ft = self.field_type(f)?;
        let h = self.hier();
        let t = if one {
            h.join(&h.make(SIG_UNIV), &ft)
        } else {
            ft
        };
        let mut ub: Option<N> = None;
        for p in h.fold(&t) {
            let mut up: Option<N> = None;
            for b in p {
                let be = self.a2k(b);
                up = Some(match up {
                    None => be,
                    Some(x) => self.ast.product(x, be),
                });
            }
            let up = up.unwrap();
            ub = Some(match ub {
                None => up,
                Some(x) => self.ast.union(x, up),
            });
        }
        let ub = ub.ok_or_else(|| fatal("field without type"))?;
        self.bounds.remove_concrete(r);
        // PardinusBounds.bound(r, upper): lower = none -> none -> ...
        let arity = self.ast.arity(ub);
        let mut lo = self.ast.none();
        for _ in 1..arity {
            let nn = self.ast.none();
            lo = self.ast.product(lo, nn);
        }
        self.bounds.symb.push((r, lo, ub));
        Ok(())
    }

    /// `BoundsComputer.size(sig, n, exact)`
    fn size(&mut self, s: SigId, mut n: i32, exact: bool) -> N {
        let a = self.a2k(s);
        if n <= 0 {
            return self.ast.mult(Mult::No, a);
        }
        if n == 1 {
            return self.ast.mult(if exact { Mult::One } else { Mult::Lone }, a);
        }
        let mut f: Option<N> = if exact { Some(self.ast.tru()) } else { None };
        let mut d: Option<N> = None;
        let mut sum: Option<N> = None;
        while n > 0 {
            n -= 1;
            let v = self.ast.var(&format!("v{}", self.cnt), 1);
            self.cnt += 1;
            let dd = self.ast.one_of(v, a);
            d = Some(match d {
                None => dd,
                Some(x) => self.ast.decls_and(dd, x),
            });
            match sum {
                None => sum = Some(v),
                Some(sm) => {
                    if let Some(ff) = f {
                        let i = self.ast.intersection(v, sm);
                        let no = self.ast.mult(Mult::No, i);
                        f = Some(self.ast.binf(no, FOp::And, ff));
                    }
                    sum = Some(self.ast.union(v, sm));
                }
            }
        }
        let (sum, d) = (sum.unwrap(), d.unwrap());
        let eq = self.ast.eq(sum, a);
        match f {
            Some(ff) => {
                let body = self.ast.binf(eq, FOp::And, ff);
                self.ast.quantify(Quant::Some, d, body)
            }
            None => {
                let no = self.ast.mult(Mult::No, a);
                let ex = self.ast.quantify(Quant::Some, d, eq);
                self.ast.binf(no, FOp::Or, ex)
            }
        }
    }
}
