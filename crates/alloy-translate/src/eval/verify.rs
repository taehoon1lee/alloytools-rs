//! Full 5-stage runtime verification (`verify_instance`) of an [`Instance`] against a semantic [`Model`] and [`Options`]:
//! 1. Scope & trace metadata
//! 2. Sig hierarchy (`extends`, `abstract`, `in`/`=`) & multiplicities (`one`/`lone`/`some`)
//! 3. Field declarations (domain, `decl` multiplicity/arrow/`defined`, `disj` groups, `enum` ordering)
//! 4. Facts & sig facts (`this` bound)
//! 5. Command formula (`run` body / `check` negated assertion)

use super::expr::eval_bool_formula;
use super::temporal::expr_is_temporal;
use super::{expr_arity, AtomIdx, RelVal, TraceEnv, Value, VerificationError, VerificationKind};
use alloy_core::sema::{FieldId, FuncId, LocalId, Model, RDecl, RExpr, SigId, SigKind};
use alloy_core::syntax::{BinOp, Const, Mult, Quant, UnOp};
use std::collections::{BTreeSet, HashMap};

use crate::{Instance, Options};

/// Independently verifies that `inst` satisfies all constraints of `model` for command `cmd_idx`.
pub fn verify_instance(
    model: &Model,
    cmd_idx: usize,
    inst: &Instance,
    opt: &Options,
) -> Result<(), VerificationError> {
    let env = TraceEnv::from_instance(model, cmd_idx, inst, opt)?;
    verify_scopes_and_meta(model, cmd_idx, &env)?;
    verify_sig_hierarchy_and_mults(model, &env)?;
    verify_fields(model, &env)?;
    verify_facts_and_sig_facts(model, &env)?;
    verify_command_formula(model, cmd_idx, &env)?;
    Ok(())
}

/// Stage 1: scope caps, exactness, static invariance, and temporal bounds.
fn verify_scopes_and_meta(
    model: &Model,
    cmd_idx: usize,
    env: &TraceEnv,
) -> Result<(), VerificationError> {
    let cmd = &model.commands[cmd_idx];
    if model.temporal {
        let (smin, smax) = cmd.steps.map_or((None, -1), |(a, b)| (a, b));
        if smax == i32::MAX {
            return Err(VerificationError::new(
                VerificationKind::ScopeViolation,
                "steps",
                "unbounded steps not supported",
            ));
        }
        let min_t = smin.unwrap_or(1).max(1) as usize;
        let max_t = (if smax > 0 { smax } else { 10 }) as usize;
        let len = env.states.len();
        if len < min_t || len > max_t {
            return Err(VerificationError::new(
                VerificationKind::ScopeViolation,
                "steps",
                format!("trace_length {len} outside {min_t}..={max_t}"),
            ));
        }
    }

    // Build children map for checking whether a sig has var descendants.
    let n_sigs = model.sigs.len();
    let mut children: Vec<Vec<SigId>> = vec![Vec::new(); n_sigs];
    for (i, s) in model.sigs.iter().enumerate() {
        if s.kind == SigKind::User && s.subset_of.is_empty() {
            if let Some(p) = s.parent {
                children[p as usize].push(i as SigId);
            }
        }
    }
    let has_var_desc = |mut start: SigId| -> bool {
        let mut stack = vec![start];
        while let Some(cur) = stack.pop() {
            if model.sigs[cur as usize].is_var {
                return true;
            }
            for &c in &children[cur as usize] {
                stack.push(c);
            }
        }
        let _ = &mut start;
        false
    };

    for (sid, sig) in model.sigs.iter().enumerate() {
        if sig.kind != SigKind::User {
            continue;
        }
        let s = sid as SigId;
        let subset_has_var = !sig.subset_of.is_empty() && has_var_ancestor(model, s);
        let sig_dynamic = sig.is_var || has_var_desc(s) || subset_has_var;
        if !sig_dynamic && env.states.len() > 1 {
            let first = &env.states[0].sigs[sid];
            for (st_i, st) in env.states.iter().enumerate().skip(1) {
                if &st.sigs[sid] != first {
                    return Err(VerificationError::new(
                        VerificationKind::SigHierarchyViolation,
                        &sig.label,
                        format!("static sig '{}' changed between state 0 and {st_i}", sig.label),
                    ));
                }
            }
        }
        if !sig.subset_of.is_empty() {
            continue;
        }
        if let Some(sc) = env.layout.scope[sid] {
            let sc = sc.max(0) as usize;
            let exact = env.layout.exact[sid];
            if !sig_dynamic {
                let len = env.states[0].sigs[sid].len();
                if exact && len != sc {
                    return Err(VerificationError::new(
                        VerificationKind::ScopeViolation,
                        &sig.label,
                        format!("exact scope mismatch for '{}': expected {sc}, got {len}", sig.label),
                    ));
                }
                if !exact && len > sc {
                    return Err(VerificationError::new(
                        VerificationKind::ScopeViolation,
                        &sig.label,
                        format!("scope exceeded for '{}': {len} > {sc}", sig.label),
                    ));
                }
            } else {
                let mut distinct = BTreeSet::new();
                for st in &env.states {
                    for tup in &st.sigs[sid].tuples {
                        distinct.insert(tup[0]);
                    }
                }
                if !exact && distinct.len() > sc {
                    return Err(VerificationError::new(
                        VerificationKind::ScopeViolation,
                        &sig.label,
                        format!("var sig '{}' uses {} > {sc} distinct atoms across trace", sig.label, distinct.len()),
                    ));
                }
                if exact && env.states[0].sigs[sid].len() != sc && distinct.len() != sc {
                    return Err(VerificationError::new(
                        VerificationKind::ScopeViolation,
                        &sig.label,
                        format!("var sig '{}' exact scope {sc} not met", sig.label),
                    ));
                }
            }
        }
    }

    for (fid, fld) in model.fields.iter().enumerate() {
        if !fld.is_var && env.states.len() > 1 {
            let first = &env.states[0].fields[fid];
            for (st_i, st) in env.states.iter().enumerate().skip(1) {
                if &st.fields[fid] != first {
                    return Err(VerificationError::new(
                        VerificationKind::FieldDeclViolation,
                        &fld.label,
                        format!("static field '{}' changed between state 0 and {st_i}", fld.label),
                    ));
                }
            }
        }
    }
    Ok(())
}

fn has_var_ancestor(model: &Model, s: SigId) -> bool {
    let mut seen = Vec::new();
    let mut stack = vec![s];
    while let Some(cur) = stack.pop() {
        if seen.contains(&cur) {
            continue;
        }
        seen.push(cur);
        let sig = &model.sigs[cur as usize];
        if sig.is_var {
            return true;
        }
        if let Some(p) = sig.parent {
            stack.push(p);
        }
        for &p in &sig.subset_of {
            stack.push(p);
        }
    }
    false
}

/// Stage 2: `extends`, disjoint siblings, `abstract`, `in`/`=`, and `one`/`lone`/`some` multiplicities.
fn verify_sig_hierarchy_and_mults(model: &Model, env: &TraceEnv) -> Result<(), VerificationError> {
    let n_sigs = model.sigs.len();
    let mut prim_children: Vec<Vec<SigId>> = vec![Vec::new(); n_sigs];
    let mut top_prims: Vec<SigId> = Vec::new();
    for (sid, sig) in model.sigs.iter().enumerate() {
        if sig.kind != SigKind::User || !sig.subset_of.is_empty() {
            continue;
        }
        match sig.parent {
            Some(p) => prim_children[p as usize].push(sid as SigId),
            None => top_prims.push(sid as SigId),
        }
    }

    // Whole-trace union per sig for temporal disjointness across time (bounds.rs `var_disjoint`).
    let mut all_state_atoms: Vec<RelVal> = Vec::with_capacity(n_sigs);
    for sid in 0..n_sigs {
        let mut acc = RelVal::empty(1);
        for st in &env.states {
            acc = acc.union(&st.sigs[sid]);
        }
        all_state_atoms.push(acc);
    }

    // Disjoint top-level PrimSigs across all states.
    for i in 0..top_prims.len() {
        for j in (i + 1)..top_prims.len() {
            let (si, sj) = (top_prims[i], top_prims[j]);
            if !all_state_atoms[si as usize].is_disjoint(&all_state_atoms[sj as usize]) {
                return Err(VerificationError::new(
                    VerificationKind::SigHierarchyViolation,
                    format!("{}, {}", model.sigs[si as usize].label, model.sigs[sj as usize].label),
                    "top-level prim sigs are not disjoint",
                ));
            }
        }
    }

    for (st_i, st) in env.states.iter().enumerate() {
        for (sid, sig) in model.sigs.iter().enumerate() {
            if sig.kind != SigKind::User {
                continue;
            }
            let val = &st.sigs[sid];
            if let Some(p) = sig.parent {
                if !val.is_subset_of(&st.sigs[p as usize]) {
                    return Err(VerificationError::new(
                        VerificationKind::SigHierarchyViolation,
                        &sig.label,
                        format!(
                            "state {st_i}: '{}' is not a subset of parent '{}'",
                            sig.label, model.sigs[p as usize].label
                        ),
                    ));
                }
            }
            if !sig.subset_of.is_empty() {
                let mut parent_union = RelVal::empty(1);
                for &p in &sig.subset_of {
                    parent_union = parent_union.union(&st.sigs[p as usize]);
                }
                if sig.is_exact {
                    if val != &parent_union {
                        return Err(VerificationError::new(
                            VerificationKind::SigHierarchyViolation,
                            &sig.label,
                            format!("state {st_i}: exact sig '{}' does not equal parent union", sig.label),
                        ));
                    }
                } else if !val.is_subset_of(&parent_union) {
                    return Err(VerificationError::new(
                        VerificationKind::SigHierarchyViolation,
                        &sig.label,
                        format!("state {st_i}: subset sig '{}' exceeds parent union", sig.label),
                    ));
                }
            }
            let kids = &prim_children[sid];
            if !kids.is_empty() {
                let mut kid_union = RelVal::empty(1);
                for &c in kids {
                    kid_union = kid_union.union(&st.sigs[c as usize]);
                }
                if sig.is_abstract && val != &kid_union {
                    return Err(VerificationError::new(
                        VerificationKind::SigHierarchyViolation,
                        &sig.label,
                        format!(
                            "state {st_i}: abstract sig '{}' != union of children (|sig|={}, |children|={})",
                            sig.label,
                            val.len(),
                            kid_union.len()
                        ),
                    ));
                }
                for a in 0..kids.len() {
                    for b in (a + 1)..kids.len() {
                        let (ca, cb) = (kids[a], kids[b]);
                        let disjoint = if model.sigs[ca as usize].is_var || model.sigs[cb as usize].is_var {
                            all_state_atoms[ca as usize].is_disjoint(&all_state_atoms[cb as usize])
                        } else {
                            st.sigs[ca as usize].is_disjoint(&st.sigs[cb as usize])
                        };
                        if !disjoint {
                            return Err(VerificationError::new(
                                VerificationKind::SigHierarchyViolation,
                                &sig.label,
                                format!(
                                    "child sigs '{}' and '{}' of '{}' overlap",
                                    model.sigs[ca as usize].label, model.sigs[cb as usize].label, sig.label
                                ),
                            ));
                        }
                    }
                }
            }
            if let Some(m) = sig.mult {
                let ok = match m {
                    Mult::One => val.len() == 1,
                    Mult::Lone => val.len() <= 1,
                    Mult::Some => !val.is_empty(),
                    Mult::Set => true,
                };
                if !ok {
                    return Err(VerificationError::new(
                        VerificationKind::SigHierarchyViolation,
                        &sig.label,
                        format!("state {st_i}: sig '{}' violates multiplicity {m:?} (len={})", sig.label, val.len()),
                    ));
                }
            }
        }
    }
    Ok(())
}

/// Stage 3: field domain, declared bound/multiplicity/defined constraint, `disj` groups, and enum ordering.
fn verify_fields(model: &Model, env: &TraceEnv) -> Result<(), VerificationError> {
    for (fid, fld) in model.fields.iter().enumerate() {
        for (st_i, st) in env.states.iter().enumerate() {
            let fv = &st.fields[fid];
            let owner_v = &st.sigs[fld.owner as usize];
            for tup in &fv.tuples {
                if !owner_v.contains(&tup[0..1]) {
                    return Err(VerificationError::new(
                        VerificationKind::FieldDeclViolation,
                        &fld.label,
                        format!(
                            "state {st_i}: field '{}' tuple starts outside owner '{}'",
                            fld.label, model.sigs[fld.owner as usize].label
                        ),
                    ));
                }
            }
        }

        let f = fid as FieldId;
        let dexpr = field_decl_expr(model, f);
        let in_expr = RExpr::Bin(
            BinOp::In,
            Box::new(RExpr::Bin(
                BinOp::Join,
                Box::new(RExpr::Local(fld.this_local)),
                Box::new(RExpr::Field(f)),
            )),
            Box::new(dexpr),
        );
        let one_owner = model.sigs[fld.owner as usize].mult == Some(Mult::One);
        let mut form = if one_owner {
            RExpr::Let(vec![(fld.this_local, RExpr::Sig(fld.owner))], Box::new(in_expr))
        } else {
            RExpr::Quant(
                Quant::All,
                vec![RDecl {
                    vars: vec![fld.this_local],
                    disjoint: false,
                    bound: RExpr::Sig(fld.owner),
                }],
                Box::new(in_expr),
            )
        };
        if fld.is_var || model.sigs[fld.owner as usize].is_var || expr_is_temporal(model, &fld.decl) {
            form = RExpr::Un(UnOp::Always, Box::new(form));
        }
        let ok = eval_bool_formula(model, env, &form, false, &[])?;
        if !ok {
            return Err(VerificationError::new(
                VerificationKind::FieldDeclViolation,
                &fld.label,
                format!("field declaration constraint failed for '{}'", fld.label),
            ));
        }
    }

    for group in &model.field_disjoint {
        if group.len() <= 1 {
            continue;
        }
        let any_var = group.iter().any(|&f| model.fields[f as usize].is_var);
        let mut dj = RExpr::Disj(group.iter().map(|&f| RExpr::Field(f)).collect());
        if any_var {
            dj = RExpr::Un(UnOp::Always, Box::new(dj));
        }
        if !eval_bool_formula(model, env, &dj, false, &[])? {
            let names: Vec<&str> = group.iter().map(|&f| model.fields[f as usize].label.as_str()).collect();
            return Err(VerificationError::new(
                VerificationKind::FieldDeclViolation,
                names.join(", "),
                "disj field constraint failed",
            ));
        }
    }

    // Verify enum ordering declaration order when the `enum_order` pattern matches (`BoundsComputer`).
    for (sid, sig) in model.sigs.iter().enumerate() {
        if sig.kind == SigKind::User && sig.mult == Some(Mult::One) && sig.fields.len() == 2 {
            verify_enum_order_if_applicable(model, env, sid as SigId)?;
        }
    }
    Ok(())
}

fn verify_enum_order_if_applicable(
    model: &Model,
    env: &TraceEnv,
    s: SigId,
) -> Result<(), VerificationError> {
    let facts: Vec<&RExpr> = model
        .sig_facts
        .iter()
        .filter(|(x, _)| *x == s)
        .map(|(_, b)| b)
        .collect();
    if facts.len() != 1 {
        return Ok(());
    }
    let (this_l, body) = match facts[0] {
        RExpr::Quant(Quant::All, ds, b) if ds.len() == 1 && ds[0].vars.len() == 1 => {
            (Some(ds[0].vars[0]), &**b)
        }
        other => (None, other),
    };
    let body = match body {
        RExpr::Block(v) if v.len() == 1 => &v[0],
        other => other,
    };
    let RExpr::TotalOrder(args) = body else { return Ok(()) };
    if args.len() != 3 {
        return Ok(());
    }
    let (f1, f2) = (model.sigs[s as usize].fields[0], model.sigs[s as usize].fields[1]);
    let (d1, d2) = (&model.fields[f1 as usize], &model.fields[f2 as usize]);
    let RExpr::Sig(sub) = d1.decl else { return Ok(()) };
    if d1.mult != Some(Mult::Set) || !model.sigs[sub as usize].is_enum {
        return Ok(());
    }
    match &d2.decl {
        RExpr::Bin(BinOp::Arrow(Mult::Set, Mult::Set), a, b)
            if **a == RExpr::Sig(sub) && **b == RExpr::Sig(sub) => {}
        _ => return Ok(()),
    }
    let is_s = |e: &RExpr| {
        matches!(e, RExpr::Sig(x) if *x == s) || matches!(e, RExpr::Local(l) if Some(*l) == this_l)
    };
    let joins = |e: &RExpr, f: FieldId| {
        matches!(e, RExpr::Bin(BinOp::Join, a, b) if is_s(a) && **b == RExpr::Field(f))
    };
    if args[0] != RExpr::Sig(sub) || !joins(&args[1], f1) || !joins(&args[2], f2) {
        return Ok(());
    }
    let kids: Vec<SigId> = (0..model.sigs.len() as SigId)
        .filter(|&c| model.sigs[c as usize].subset_of.is_empty() && model.sigs[c as usize].parent == Some(sub))
        .collect();
    if kids.is_empty() {
        return Ok(());
    }
    let st = &env.states[0];
    let s_atom = match st.sigs[s as usize].tuples.first() {
        Some(t) => t[0],
        None => return Ok(()),
    };
    let mut kid_atoms: Vec<AtomIdx> = Vec::with_capacity(kids.len());
    for &c in &kids {
        if st.sigs[c as usize].len() != 1 {
            return Ok(());
        }
        kid_atoms.push(st.sigs[c as usize].tuples[0][0]);
    }
    let expected_first = RelVal::singleton(2, vec![s_atom, kid_atoms[0]]);
    let expected_next = RelVal::from_tuples(
        3,
        kid_atoms
            .windows(2)
            .map(|w| vec![s_atom, w[0], w[1]])
            .collect(),
    );
    if st.fields[f1 as usize] != expected_first || st.fields[f2 as usize] != expected_next {
        return Err(VerificationError::new(
            VerificationKind::FieldDeclViolation,
            &model.sigs[s as usize].label,
            "enum ordering First/Next does not match declaration order",
        ));
    }
    Ok(())
}

fn field_decl_expr(model: &Model, f: FieldId) -> RExpr {
    let fd = &model.fields[f as usize];
    match fd.mult {
        Some(m) => {
            let op = match m {
                Mult::Set => UnOp::Set,
                Mult::One => UnOp::One,
                Mult::Lone => UnOp::Lone,
                Mult::Some => UnOp::Some,
            };
            RExpr::Un(op, Box::new(fd.decl.clone()))
        }
        None if fd.defined => RExpr::Un(UnOp::ExactlyOf, Box::new(fd.decl.clone())),
        None => {
            let ar = expr_arity(model, &fd.decl);
            if ar == 1 && !matches!(fd.decl, RExpr::Bin(BinOp::Arrow(..), ..)) {
                RExpr::Un(UnOp::One, Box::new(fd.decl.clone()))
            } else {
                fd.decl.clone()
            }
        }
    }
}

/// Stage 4: global `model.facts` and per-sig `model.sig_facts`.
fn verify_facts_and_sig_facts(model: &Model, env: &TraceEnv) -> Result<(), VerificationError> {
    for (idx, fact) in model.facts.iter().enumerate() {
        if !eval_bool_formula(model, env, &fact.body, false, &[])? {
            let name = fact.name.as_deref().unwrap_or("unnamed");
            return Err(VerificationError::new(
                VerificationKind::FactFailed,
                format!("fact#{idx}({name})"),
                format!("fact '{name}' evaluated to false"),
            ));
        }
    }

    for &(sid, ref body) in &model.sig_facts {
        if let RExpr::Quant(Quant::All, _, b) = body {
            if matches!(&**b, RExpr::Block(v) if v.is_empty()) {
                continue;
            }
        }
        let one = model.sigs[sid as usize].mult == Some(Mult::One);
        let mut form = if one {
            match body {
                RExpr::Quant(Quant::All, ds, b) if ds.len() == 1 => {
                    subst_local(b, ds[0].vars[0], &RExpr::Sig(sid))
                }
                other => other.clone(),
            }
        } else {
            body.clone()
        };
        if model.sigs[sid as usize].is_var || expr_is_temporal(model, &form) {
            form = RExpr::Un(UnOp::Always, Box::new(form));
        }
        if !eval_bool_formula(model, env, &form, false, &[])? {
            return Err(VerificationError::new(
                VerificationKind::SigFactFailed,
                &model.sigs[sid as usize].label,
                format!("sig fact failed for '{}'", model.sigs[sid as usize].label),
            ));
        }
    }
    Ok(())
}

/// Stage 5: command formula (`run` body or `check` negated assertion).
fn verify_command_formula(
    model: &Model,
    cmd_idx: usize,
    env: &TraceEnv,
) -> Result<(), VerificationError> {
    let cmd = &model.commands[cmd_idx];
    if cmd.check {
        // An instance of `check A` must make A false (so `!A` is true).
        let ok = eval_bool_formula(model, env, &cmd.formula, true, &[])?;
        if !ok {
            return Err(VerificationError::new(
                VerificationKind::AssertionNotViolated,
                &cmd.name,
                format!("counterexample does not violate assertion '{}'", cmd.name),
            ));
        }
        return Ok(());
    }

    // Mirror exact/facts.rs `command_expr`: `run <fun>` checks `body in ret`!
    let expr = command_run_expr(model, &cmd.formula);
    if !eval_bool_formula(model, env, &expr, false, &[])? {
        return Err(VerificationError::new(
            VerificationKind::CommandFormulaFailed,
            &cmd.name,
            format!("command formula '{}' evaluated to false", cmd.name),
        ));
    }
    Ok(())
}

fn command_run_expr(model: &Model, f: &RExpr) -> RExpr {
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
    let body_of = |fid: FuncId| -> RExpr {
        let func = &model.funcs[fid as usize];
        if func.is_pred {
            func.body.clone()
        } else {
            let ret = func.ret.clone().unwrap_or(RExpr::Const(Const::Univ));
            RExpr::Bin(BinOp::In, Box::new(func.body.clone()), Box::new(ret))
        }
    };
    match f {
        RExpr::Quant(Quant::Some, decls, inner) => match target(inner) {
            Some(fid) => {
                let b = body_of(fid);
                RExpr::Quant(Quant::Some, decls.clone(), Box::new(b))
            }
            None => f.clone(),
        },
        _ => match target(f) {
            Some(fid) if model.funcs[fid as usize].params.is_empty() => body_of(fid),
            _ => f.clone(),
        },
    }
}

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

/// Public helper kept for direct formula queries under custom local environments.
#[allow(dead_code)]
pub(crate) fn eval_under(
    model: &Model,
    env: &TraceEnv,
    expr: &RExpr,
    locals: &[(LocalId, Value, RExpr)],
) -> Result<bool, crate::eval::EvalError> {
    eval_bool_formula(model, env, expr, false, locals)
}

pub(crate) fn _unused_marker(_v: &Value, _m: &HashMap<String, AtomIdx>) {}

#[cfg(test)]
mod mutation_tests {
    use super::*;
    use crate::{execute_command, Options};
    use alloy_core::sema;

    fn solve_src(files: &[(&str, &str)], main_file: &str, opt: &Options) -> (alloy_core::sema::Model, Instance) {
        static N: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(9000);
        let n = N.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let dir = std::env::temp_dir().join(format!("alloy_rs_eval_mut_{}_{}", std::process::id(), n));
        std::fs::create_dir_all(&dir).unwrap();
        for (name, content) in files {
            std::fs::write(dir.join(name), content).unwrap();
        }
        let world = alloy_core::parse_everything_from_file(&dir.join(main_file)).unwrap();
        let model = sema::build(&world.modules).unwrap();
        let sol = execute_command(&world, 0, opt).unwrap();
        assert!(sol.sat, "test model must be SAT");
        (model, sol.instance().unwrap())
    }

    fn single(src: &str) -> (Model, Instance) {
        solve_src(&[("m.als", src)], "m.als", &Options::default())
    }

    #[test]
    fn mutation_01_static_run_add_unknown_atom_and_drop_tuple() {
        let (m, mut inst) = single("sig A {}\nfact { some A }\nrun {} for 2\n");
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        let mut bad = inst.clone();
        bad.states[0].get_mut("this/A").unwrap().clear();
        assert_eq!(verify_instance(&m, 0, &bad, &Options::default()).unwrap_err().kind, VerificationKind::FactFailed);
        inst.states[0].get_mut("this/A").unwrap().extend([vec!["A$9".into()], vec!["A$10".into()], vec!["A$11".into()]]);
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_err());
    }

    #[test]
    fn mutation_02_check_counterexample_made_valid_fails_assertion_not_violated() {
        let (m, mut inst) = single("sig A { f: lone A }\nassert sym { all x, y: A | x->y in f implies y->x in f }\ncheck sym for exactly 2 A\n");
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        // Make f symmetric (empty) so the assertion actually holds -> invalid counterexample
        inst.states[0].get_mut("this/A.f").unwrap().clear();
        assert_eq!(
            verify_instance(&m, 0, &inst, &Options::default()).unwrap_err().kind,
            VerificationKind::AssertionNotViolated
        );
    }

    #[test]
    fn mutation_03_scope_exact_violation() {
        let (m, mut inst) = single("sig A {}\nrun {} for exactly 2 A\n");
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        inst.states[0].get_mut("this/A").unwrap().pop();
        assert_eq!(
            verify_instance(&m, 0, &inst, &Options::default()).unwrap_err().kind,
            VerificationKind::ScopeViolation
        );
    }

    #[test]
    fn mutation_04_scope_upper_exceeded() {
        let (m, mut inst) = single("sig A {}\nrun {} for 2 A\n");
        inst.states[0].insert("this/A".into(), vec![vec!["A$0".into()], vec!["A$1".into()], vec!["A$2".into()]]);
        assert_eq!(
            verify_instance(&m, 0, &inst, &Options::default()).unwrap_err().kind,
            VerificationKind::ScopeViolation
        );
    }

    #[test]
    fn mutation_05_extends_parent_subset_violation() {
        let (m, mut inst) = single("sig P {}\nsig C extends P {}\nrun { some C } for 3\n");
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        inst.states[0].get_mut("this/P").unwrap().clear();
        assert_eq!(
            verify_instance(&m, 0, &inst, &Options::default()).unwrap_err().kind,
            VerificationKind::SigHierarchyViolation
        );
    }

    #[test]
    fn mutation_06_extends_siblings_overlap_violation() {
        let (m, mut inst) = single("sig P {}\nsig C1, C2 extends P {}\nrun { some C1 and some C2 } for 3\n");
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        let a0 = inst.states[0]["this/C1"][0].clone();
        inst.states[0].get_mut("this/C2").unwrap().push(a0);
        inst.states[0].get_mut("this/C2").unwrap().sort();
        inst.states[0].get_mut("this/C2").unwrap().dedup();
        assert_eq!(
            verify_instance(&m, 0, &inst, &Options::default()).unwrap_err().kind,
            VerificationKind::SigHierarchyViolation
        );
    }

    #[test]
    fn mutation_07_abstract_sig_remainder_violation() {
        let (m, mut inst) = single("abstract sig P {}\nsig C1 extends P {}\nrun {} for 2\n");
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        inst.states[0].insert("this/P".into(), vec![vec!["C1$0".into()]]);
        inst.states[0].insert("this/C1".into(), vec![]);
        assert_eq!(
            verify_instance(&m, 0, &inst, &Options::default()).unwrap_err().kind,
            VerificationKind::SigHierarchyViolation
        );
    }

    #[test]
    fn mutation_08_subset_sig_in_and_equal_violation() {
        let (m, mut inst) = single("sig A {}\nsig B in A {}\nsig C = A {}\nrun { some A and some B } for 2\n");
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        let mut b1 = inst.clone();
        b1.states[0].insert("this/C".into(), vec![]);
        assert_eq!(
            verify_instance(&m, 0, &b1, &Options::default()).unwrap_err().kind,
            VerificationKind::SigHierarchyViolation
        );
        inst.states[0].insert("this/B".into(), vec![vec!["X$9".into()]]);
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_err());
    }

    #[test]
    fn mutation_09_sig_multiplicities_one_lone_some() {
        let (m, inst) = single("one sig OneS {}\nsome sig SomeS {}\nlone sig LoneS {}\nrun {} for 2\n");
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        let mut b1 = inst.clone();
        b1.states[0].insert("this/SomeS".into(), vec![]);
        assert_eq!(
            verify_instance(&m, 0, &b1, &Options::default()).unwrap_err().kind,
            VerificationKind::SigHierarchyViolation
        );
        let mut b2 = inst.clone();
        b2.states[0].insert("this/LoneS".into(), vec![vec!["LoneS$0".into()], vec!["LoneS$1".into()]]);
        assert_eq!(
            verify_instance(&m, 0, &b2, &Options::default()).unwrap_err().kind,
            VerificationKind::ScopeViolation
        );
        let mut b3 = inst;
        b3.states[0].insert("this/OneS".into(), vec![]);
        assert_eq!(
            verify_instance(&m, 0, &b3, &Options::default()).unwrap_err().kind,
            VerificationKind::ScopeViolation
        );
    }

    #[test]
    fn mutation_10_field_default_one_multiplicity_violation() {
        let (m, mut inst) = single("sig B {}\nsig A { b: B }\nrun { one A } for 2\n");
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        inst.states[0].insert("this/A.b".into(), vec![]);
        assert_eq!(
            verify_instance(&m, 0, &inst, &Options::default()).unwrap_err().kind,
            VerificationKind::FieldDeclViolation
        );
    }

    #[test]
    fn mutation_11_field_arrow_multiplicity_violation() {
        let (m, mut inst) = single("sig B {}\nsig A { r: B one -> one B }\nrun { some A and #B = 2 } for 2\n");
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        inst.states[0].get_mut("this/A.r").unwrap().pop();
        assert_eq!(
            verify_instance(&m, 0, &inst, &Options::default()).unwrap_err().kind,
            VerificationKind::FieldDeclViolation
        );
    }

    #[test]
    fn mutation_12_field_disjoint_and_defined_field_violation() {
        let (m, inst) = single("sig B {}\nsig A { disj f, g: set B, h = f + g }\nrun { some A and some A.f and some A.g } for 2\n");
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        let mut b1 = inst.clone();
        let af0 = b1.states[0]["this/A.f"][0].clone();
        b1.states[0].get_mut("this/A.g").unwrap().push(af0);
        b1.states[0].get_mut("this/A.g").unwrap().sort();
        b1.states[0].get_mut("this/A.g").unwrap().dedup();
        assert_eq!(
            verify_instance(&m, 0, &b1, &Options::default()).unwrap_err().kind,
            VerificationKind::FieldDeclViolation
        );
        let mut b2 = inst;
        b2.states[0].insert("this/A.h".into(), vec![]);
        assert_eq!(
            verify_instance(&m, 0, &b2, &Options::default()).unwrap_err().kind,
            VerificationKind::FieldDeclViolation
        );
    }

    #[test]
    fn mutation_13_enum_order_violation() {
        let (m, mut inst) = single("enum E { A, B, C }\nsig X { e: one E }\nrun {} for 1 X\n");
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        // Swap enum order in Ord.First from A$0 to B$0
        let first_key = inst.states[0].keys().find(|k| k.ends_with("/Ord.First")).unwrap().clone();
        let b_atom = inst.states[0]["this/B"][0][0].clone();
        inst.states[0].get_mut(&first_key).unwrap()[0][1] = b_atom;
        assert_eq!(
            verify_instance(&m, 0, &inst, &Options::default()).unwrap_err().kind,
            VerificationKind::FieldDeclViolation
        );
    }

    #[test]
    fn mutation_14_sig_fact_violation() {
        let (m, mut inst) = single("sig A { x: set A } { this !in x }\nrun { some x } for 2\n");
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        let a0 = inst.states[0]["this/A"][0][0].clone();
        inst.states[0].get_mut("this/A.x").unwrap().push(vec![a0.clone(), a0]);
        assert_eq!(
            verify_instance(&m, 0, &inst, &Options::default()).unwrap_err().kind,
            VerificationKind::SigFactFailed
        );
    }

    #[test]
    fn mutation_15_int_arithmetic_and_card_and_command_formula() {
        let (m, mut inst) = single("sig A {}\nrun { #A = 2 and plus[1, 1] = 2 } for 3\n");
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        inst.states[0].get_mut("this/A").unwrap().pop();
        assert_eq!(
            verify_instance(&m, 0, &inst, &Options::default()).unwrap_err().kind,
            VerificationKind::CommandFormulaFailed
        );
    }

    #[test]
    fn mutation_16_seq_contiguity_violation() {
        let (m, mut inst) = single("sig Item {}\none sig Holder { s: seq Item }\nrun { #Holder.s = 2 } for 2 but 4 int\n");
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        // Shift index 1 to 2 creating a gap [0, 2]
        let s_vec = inst.states[0].get_mut("this/Holder.s").unwrap();
        for t in s_vec.iter_mut() {
            if t[1] == "1" {
                t[1] = "2".into();
            }
        }
        assert_eq!(
            verify_instance(&m, 0, &inst, &Options::default()).unwrap_err().kind,
            VerificationKind::FieldDeclViolation
        );
    }

    #[test]
    fn mutation_17_int_no_overflow_evaluator_check() {
        let mut opt = Options::default();
        opt.no_overflow = false;
        let (m, inst) = single("sig A { n: one Int }\nrun { some A and A.n = plus[5, 5] } for 1 A, 4 int\n");
        assert!(verify_instance(&m, 0, &inst, &opt).is_ok());
        // 5 + 5 = -6 in 4-bit two's complement -> overflows when no_overflow = true
        let mut opt_nof = Options::default();
        opt_nof.no_overflow = true;
        assert_eq!(
            verify_instance(&m, 0, &inst, &opt_nof).unwrap_err().kind,
            VerificationKind::CommandFormulaFailed
        );
    }

    #[test]
    fn mutation_18_temporal_loop_state_change_fails() {
        let (m, mut inst) = single("var sig P {}\nrun { some P and after no P and always (no P implies after no P) } for 2 but 2 steps\n");
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        assert_eq!(inst.states.len(), 2);
        // Flip loop state from 1 back to 0: then P cannot stay empty forever because state 0 has some P
        inst.loop_state = 0;
        assert_eq!(
            verify_instance(&m, 0, &inst, &Options::default()).unwrap_err().kind,
            VerificationKind::CommandFormulaFailed
        );
    }

    #[test]
    fn mutation_19_temporal_static_sig_mutated_between_states_fails() {
        let (m, mut inst) = single("sig S {}\nvar sig P in S {}\nrun { some P and after no P } for 2 but 2 steps\n");
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        inst.states[1].get_mut("this/S").unwrap().clear();
        assert_eq!(
            verify_instance(&m, 0, &inst, &Options::default()).unwrap_err().kind,
            VerificationKind::SigHierarchyViolation
        );
    }

    #[test]
    fn mutation_20_temporal_past_since_and_before_multi_unroll() {
        let (m, mut inst) = single(
            "sig U {}\nvar sig P in U {}\nvar sig Q in U {}\nrun { P != Q and after (some P and before some Q) and always (Q' = P) } for 2 but 2..3 steps\n",
        );
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        // Drop Q from state 0 -> `before some Q` at state 1 becomes false
        inst.states[0].get_mut("this/Q").unwrap().clear();
        assert_eq!(
            verify_instance(&m, 0, &inst, &Options::default()).unwrap_err().kind,
            VerificationKind::CommandFormulaFailed
        );
    }

    #[test]
    fn mutation_21_opened_module_paths_match_eval_and_verify() {
        let helper = "module helper[T]\none sig Box { v: one T }\n";
        let main = "open helper[A] as h1\nopen helper[B] as h2\nsig A {}\nsig B {}\nrun { some h1/Box.v and some h2/Box.v } for 2\n";
        let (m, mut inst) = solve_src(&[("helper.als", helper), ("main.als", main)], "main.als", &Options::default());
        assert!(verify_instance(&m, 0, &inst, &Options::default()).is_ok());
        inst.states[0].get_mut("h1/Box.v").unwrap().clear();
        assert_eq!(
            verify_instance(&m, 0, &inst, &Options::default()).unwrap_err().kind,
            VerificationKind::FieldDeclViolation
        );
    }
}
