//! `TranslateAlloyToKodkod.makeFacts` and the Java command formula (`CompModule.resolveCommand`).

use super::*;

impl<'a> Cx<'a> {
    /// The Java `d.expr` of a field declaration (multiplicity keyword restored; a unary bound without one is ONEOF).
    fn field_decl_expr(&mut self, f: FieldId) -> Result<RExpr, AlloyError> {
        let fd = self.model.fields[f as usize].clone();
        Ok(match fd.mult {
            Some(m) => {
                let op = match m {
                    AMult::Set => UnOp::Set,
                    AMult::One => UnOp::One,
                    AMult::Lone => UnOp::Lone,
                    AMult::Some => UnOp::Some,
                };
                RExpr::Un(op, Box::new(fd.decl.clone()))
            }
            None if fd.defined => RExpr::Un(UnOp::ExactlyOf, Box::new(fd.decl.clone())),
            None => {
                let ar = self
                    .field_type(f)?
                    .entries
                    .first()
                    .map(|e| e.len())
                    .unwrap_or(2)
                    - 1;
                if ar == 1 && !matches!(fd.decl, RExpr::Bin(BinOp::Arrow(..), ..)) {
                    RExpr::Un(UnOp::One, Box::new(fd.decl.clone()))
                } else {
                    fd.decl.clone()
                }
            }
        })
    }

    /// `TranslateAlloyToKodkod.makeFacts(cmd.formula)`
    pub(super) fn make_facts(&mut self) -> Result<(), AlloyError> {
        let sigs = self.alloc_order.clone();
        for &s in &sigs {
            let one = self.is_one(s);
            let fields = self.model.sigs[s as usize].fields.clone();
            let mut k = 0;
            while k < fields.len() {
                // a decl group: the fields of one `disj` group declared together, else one field
                let group: Vec<FieldId> = match self
                    .model
                    .field_disjoint
                    .iter()
                    .find(|g| g.first() == Some(&fields[k]))
                {
                    Some(g) => g.clone(),
                    None => vec![fields[k]],
                };
                k += group.len();
                for &f in &group {
                    let this_l = self.model.fields[f as usize].this_local;
                    let oldt = self.ltypes.len();
                    self.bind_type(this_l, &RExpr::Sig(s));
                    let dexpr = self.field_decl_expr(f)?;
                    let inr = RExpr::Bin(
                        BinOp::In,
                        Box::new(RExpr::Bin(
                            BinOp::Join,
                            Box::new(RExpr::Local(this_l)),
                            Box::new(RExpr::Field(f)),
                        )),
                        Box::new(dexpr),
                    );
                    let form = if one {
                        RExpr::Let(vec![(this_l, RExpr::Sig(s))], Box::new(inr))
                    } else {
                        RExpr::Quant(
                            AQuant::All,
                            vec![RDecl {
                                vars: vec![this_l],
                                disjoint: false,
                                bound: RExpr::Sig(s),
                            }],
                            Box::new(inr),
                        )
                    };
                    let mut ff = self.cform(&form)?;
                    self.ltypes.truncate(oldt);
                    if self.is_temporal(ff) {
                        ff = self.always(ff);
                    }
                    self.add_formula(ff);
                    // [electrum] a variable singleton sig is not simplified
                    if !one || self.is_var_sig(s) {
                        let mut fr = self.a2k_field[f as usize].unwrap();
                        let ar = self
                            .field_type(f)?
                            .entries
                            .first()
                            .map(|e| e.len())
                            .unwrap_or(1);
                        for _ in 1..ar {
                            let u = self.ast.univ();
                            fr = self.ast.join(fr, u);
                        }
                        let se = self.a2k(s);
                        let mut ff = self.ast.in_(fr, se);
                        if self.is_temporal(ff) {
                            ff = self.always(ff);
                        }
                        self.add_formula(ff);
                    }
                }
                if group.len() > 1 {
                    let dj = RExpr::Disj(group.iter().map(|f| RExpr::Field(*f)).collect());
                    let mut ff = self.cform(&dj)?;
                    if self.model.fields[group[0] as usize].is_var {
                        ff = self.always(ff);
                    }
                    self.add_formula(ff);
                }
            }
            let facts: Vec<RExpr> = self
                .model
                .sig_facts
                .iter()
                .filter(|(x, _)| *x == s)
                .map(|(_, b)| b.clone())
                .collect();
            for body in facts {
                // an empty appended fact `{ }` is TRUE and skipped (CompModule.resolveFacts)
                if let RExpr::Quant(AQuant::All, _, b) = &body {
                    if matches!(&**b, RExpr::Block(v) if v.is_empty()) {
                        continue;
                    }
                }
                // a `one` sig's appended fact is resolved with `this` bound to the sig itself
                let form = if one {
                    match body {
                        RExpr::Quant(AQuant::All, ds, b) if ds.len() == 1 => {
                            subst_local(&b, ds[0].vars[0], &RExpr::Sig(s))
                        }
                        other => other,
                    }
                } else {
                    body
                };
                let mut ff = self.cform(&form).map_err(|e| {
                    fatal(format!(
                        "sig fact of {}: {}",
                        self.labels[s as usize], e.msg
                    ))
                })?;
                // [electrum] a sig fact over variable relations holds in every state
                if self.is_temporal(ff) {
                    ff = self.always(ff);
                }
                self.add_formula(ff);
            }
        }
        // the command formula: globalFacts.and(e), flattened by ExprList.makeAND; one formula per conjunct
        let mut parts: Vec<RExpr> = Vec::new();
        for f in &self.model.facts {
            parts.push(f.body.clone());
        }
        let e = self.command_expr()?;
        parts.push(e);
        let whole = RExpr::Block(parts);
        let mut fs: Vec<&RExpr> = Vec::new();
        visit::flatten_top(&whole, &mut fs);
        let fs: Vec<RExpr> = fs.into_iter().cloned().collect();
        for (ci, x) in fs.iter().enumerate() {
            let ff = self
                .cform(x)
                .map_err(|e| fatal(format!("command conjunct #{ci}: {}", e.msg)))?;
            self.add_formula(ff);
        }
        Ok(())
    }

    /// Java's command `e`: `!assert` for check; the pred body (`body in returnDecl` for a fun), quantified over
    /// the parameters, for `run f`; the block of `run { ... }`.
    fn command_expr(&mut self) -> Result<RExpr, AlloyError> {
        let f = self.cmd.formula.clone();
        if self.cmd.check {
            return Ok(RExpr::Un(UnOp::Not, Box::new(f)));
        }
        fn target(e: &RExpr) -> Option<FuncId> {
            match e {
                RExpr::Call(fid, _) => Some(*fid),
                RExpr::Un(UnOp::Some, c) => match &**c {
                    RExpr::Call(fid, _) => Some(*fid),
                    _ => None,
                },
                _ => None,
            }
        }
        let body_of = |cx: &Self, fid: FuncId| -> RExpr {
            let func = &cx.model.funcs[fid as usize];
            if func.is_pred {
                func.body.clone()
            } else {
                let ret = func.ret.clone().unwrap_or(RExpr::Const(Const::Univ));
                RExpr::Bin(BinOp::In, Box::new(func.body.clone()), Box::new(ret))
            }
        };
        match &f {
            RExpr::Quant(AQuant::Some, decls, inner) => match target(inner) {
                Some(fid) => {
                    let b = body_of(self, fid);
                    Ok(RExpr::Quant(AQuant::Some, decls.clone(), Box::new(b)))
                }
                None => Ok(f),
            },
            _ => match target(&f) {
                Some(fid) if self.model.funcs[fid as usize].params.is_empty() => {
                    Ok(body_of(self, fid))
                }
                _ => Ok(f),
            },
        }
    }
}

/// Replaces every `Local(l)` by `by`.
fn subst_local(e: &RExpr, l: LocalId, by: &RExpr) -> RExpr {
    let r = |x: &RExpr| subst_local(x, l, by);
    let rd = |d: &RDecl| RDecl {
        vars: d.vars.clone(),
        disjoint: d.disjoint,
        bound: r(&d.bound),
    };
    match e {
        RExpr::Local(x) if *x == l => by.clone(),
        RExpr::Un(op, x) => RExpr::Un(*op, Box::new(r(x))),
        RExpr::Bin(op, a, b) => RExpr::Bin(*op, Box::new(r(a)), Box::new(r(b))),
        RExpr::Quant(q, ds, b) => RExpr::Quant(*q, ds.iter().map(rd).collect(), Box::new(r(b))),
        RExpr::Compr(ds, b) => RExpr::Compr(ds.iter().map(rd).collect(), Box::new(r(b))),
        RExpr::Ite(c, a, b) => RExpr::Ite(Box::new(r(c)), Box::new(r(a)), Box::new(r(b))),
        RExpr::Let(bs, b) => {
            RExpr::Let(bs.iter().map(|(x, v)| (*x, r(v))).collect(), Box::new(r(b)))
        }
        RExpr::Call(f, args) => RExpr::Call(*f, args.iter().map(r).collect()),
        RExpr::Block(xs) => RExpr::Block(xs.iter().map(r).collect()),
        RExpr::Disj(xs) => RExpr::Disj(xs.iter().map(r).collect()),
        RExpr::TotalOrder(xs) => RExpr::TotalOrder(xs.iter().map(r).collect()),
        RExpr::Choice(xs) => RExpr::Choice(xs.iter().map(r).collect()),
        other => other.clone(),
    }
}
