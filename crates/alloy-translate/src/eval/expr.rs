//! Direct Alloy `RExpr` evaluator over [`TraceEnv`] with Alloy 6 temporal lasso semantics,
//! two's-complement bitwidth wrapping, `no_overflow` propagation, `Choice` resolution, and sound skolem witness hints.

use super::temporal::{expr_is_temporal, past_depth, TimeHorizon};
use super::{expr_arity, wrap_int, AtomIdx, EvalError, RelVal, TraceEnv, Value};
use alloy_core::sema::{FuncId, LocalId, Model, RDecl, RExpr, SIG_INT, SIG_SEQINT};
use alloy_core::syntax::{BinOp, Const, Mult, Quant, UnOp};
use std::collections::{BTreeSet, HashMap};
use std::hash::{Hash, Hasher};

use crate::resolve::{is_choice, type_of, Exp, Resolver, TupleSet as RTs};

#[derive(Debug, Clone)]
struct EvalVal {
    val: Value,
    of: bool,
}

#[derive(Debug, Clone, Copy)]
struct BoolRes {
    val: bool,
    of: bool,
}

/// Evaluates `expr` on `model` and `env` at state index `state`.
pub fn eval_expr(
    model: &Model,
    env: &TraceEnv,
    expr: &RExpr,
    state: usize,
) -> Result<Value, EvalError> {
    if state >= env.states.len() {
        return Err(EvalError::new(format!(
            "state index {state} out of bounds ({})",
            env.states.len()
        )));
    }
    let h = past_depth(model, expr);
    let horizon = TimeHorizon::new(env.states.len(), env.loop_state, h);
    let mut ctx = EvalCtx::new(model, env, horizon);
    let r = ctx.eval_val(expr, state, false)?;
    if env.no_overflow && r.of {
        if let Value::Bool(_) = r.val {
            return Ok(Value::Bool(false));
        }
    }
    Ok(r.val)
}

pub(crate) fn eval_bool_formula(
    model: &Model,
    env: &TraceEnv,
    expr: &RExpr,
    negated: bool,
    initial_locals: &[(LocalId, Value, RExpr)],
) -> Result<bool, EvalError> {
    let h = past_depth(model, expr);
    let horizon = TimeHorizon::new(env.states.len(), env.loop_state, h);
    let mut ctx = EvalCtx::new(model, env, horizon);
    for (l, v, ty_e) in initial_locals {
        ctx.locals.push((*l, v.clone()));
        let ty = ctx.rty(ty_e).unwrap_or_else(EvalCtx::empty_ty);
        ctx.ltypes.push((*l, ty));
    }
    let res = ctx.eval_bool_pol(expr, 0, negated)?;
    Ok(if env.no_overflow && res.of { false } else { res.val })
}

struct EvalCtx<'a> {
    model: &'a Model,
    env: &'a TraceEnv,
    horizon: TimeHorizon,
    locals: Vec<(LocalId, Value)>,
    lazy: Vec<(LocalId, RExpr)>,
    ltypes: Vec<(LocalId, RTs)>,
    call_stack: Vec<FuncId>,
    temp_memo: HashMap<(usize, usize, u64), BoolRes>,
    zero_arg_cache: HashMap<(FuncId, usize), EvalVal>,
    ty_memo: Vec<Option<RTs>>,
}

impl<'a> Resolver for EvalCtx<'a> {
    fn model(&self) -> &Model {
        self.model
    }

    fn rty(&mut self, e: &RExpr) -> Option<RTs> {
        self.rty_with(e, &[])
    }
}

impl<'a> EvalCtx<'a> {
    fn empty_ty() -> RTs {
        RTs::from_tuples(1, std::iter::empty::<Vec<u32>>())
    }

    fn rty_with(&mut self, e: &RExpr, extra: &[(LocalId, RTs)]) -> Option<RTs> {
        let lay = &self.env.layout;
        let max_int = self.env.universe.max_int;
        let min_int = self.env.universe.min_int;
        let n_atoms = lay.atoms.len() as u32
            + if max_int >= min_int {
                (max_int - min_int + 1) as u32
            } else {
                0
            };
        let mut memo = std::mem::take(&mut self.ty_memo);
        let mut type_env: HashMap<LocalId, RTs> =
            HashMap::with_capacity(self.ltypes.len() + extra.len());
        for (lid, ty) in &self.ltypes {
            type_env.insert(*lid, ty.clone());
        }
        for (lid, ty) in extra {
            type_env.insert(*lid, ty.clone());
        }
        let r = type_of(
            self.model,
            lay,
            n_atoms,
            e,
            &mut memo,
            &mut Vec::new(),
            &mut type_env,
        )
        .ok();
        self.ty_memo = memo;
        r
    }

    fn new(model: &'a Model, env: &'a TraceEnv, horizon: TimeHorizon) -> Self {
        EvalCtx {
            model,
            env,
            horizon,
            locals: Vec::new(),
            lazy: Vec::new(),
            ltypes: Vec::new(),
            call_stack: Vec::new(),
            temp_memo: HashMap::new(),
            zero_arg_cache: HashMap::new(),
            ty_memo: vec![None; model.fields.len()],
        }
    }

    #[inline]
    fn st(&self, t: usize) -> usize {
        self.horizon.state_of(t)
    }

    fn local_get(&self, l: LocalId) -> Option<&Value> {
        self.locals.iter().rev().find(|(id, _)| *id == l).map(|(_, v)| v)
    }

    fn lazy_get(&self, l: LocalId) -> Option<RExpr> {
        self.lazy.iter().rev().find(|(id, _)| *id == l).map(|(_, e)| e.clone())
    }

    fn env_hash(&self) -> u64 {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        self.locals.len().hash(&mut h);
        for (l, v) in &self.locals {
            l.hash(&mut h);
            match v {
                Value::Bool(b) => {
                    0u8.hash(&mut h);
                    b.hash(&mut h);
                }
                Value::Int(i) => {
                    1u8.hash(&mut h);
                    i.hash(&mut h);
                }
                Value::Rel(r) => {
                    2u8.hash(&mut h);
                    r.hash(&mut h);
                }
            }
        }
        self.lazy.len().hash(&mut h);
        for (l, _) in &self.lazy {
            l.hash(&mut h);
        }
        h.finish()
    }

    fn val_to_rel(&self, v: Value) -> Result<RelVal, EvalError> {
        match v {
            Value::Rel(r) => Ok(r),
            Value::Int(i) => Ok(match self.env.universe.int_atom.get(&i) {
                Some(&a) => RelVal::singleton(1, vec![a]),
                None => RelVal::empty(1),
            }),
            Value::Bool(b) => Err(EvalError::new(format!("expected relation, got bool {b}"))),
        }
    }

    fn val_to_int(&self, v: EvalVal) -> Result<(i32, bool), EvalError> {
        match v.val {
            Value::Int(i) => Ok((i, v.of)),
            Value::Rel(r) => {
                if r.arity != 1 {
                    return Err(EvalError::new(format!(
                        "cannot convert arity-{} relation to int",
                        r.arity
                    )));
                }
                let mut ints = Vec::new();
                for tup in &r.tuples {
                    if let Some(iv) = self.env.universe.int_val[tup[0].0 as usize] {
                        ints.push(iv);
                    }
                }
                let (s, sum_of) = sum_slice(&ints, self.env.bitwidth);
                Ok((s, v.of || sum_of))
            }
            Value::Bool(b) => Err(EvalError::new(format!("expected int, got bool {b}"))),
        }
    }

    fn eval_rel(&mut self, expr: &RExpr, t: usize) -> Result<(RelVal, bool), EvalError> {
        let r = self.eval_val(expr, t, false)?;
        let of = r.of;
        Ok((self.val_to_rel(r.val)?, of))
    }

    fn eval_int(&mut self, expr: &RExpr, t: usize) -> Result<(i32, bool), EvalError> {
        let r = self.eval_val(expr, t, false)?;
        self.val_to_int(r)
    }

    fn eval_bool_pol(
        &mut self,
        expr: &RExpr,
        t: usize,
        negated: bool,
    ) -> Result<BoolRes, EvalError> {
        // Memoize pure temporal expressions by (expr pointer, time, local env hash).
        if self.lazy.is_empty()
            && matches!(
            expr,
            RExpr::Un(
                UnOp::Always
                    | UnOp::Eventually
                    | UnOp::Historically
                    | UnOp::Once
                    | UnOp::Before
                    | UnOp::After,
                _
            ) | RExpr::Bin(
                BinOp::Until | BinOp::Releases | BinOp::Since | BinOp::Triggered,
                _,
                _
            )
        ) {
            let eh = self.env_hash();
            let key = ((expr as *const RExpr as usize) ^ ((negated as usize) << 63), t, eh);
            if let Some(&cached) = self.temp_memo.get(&key) {
                return Ok(cached);
            }
            let r = self.eval_bool_pol_inner(expr, t, negated)?;
            self.temp_memo.insert(key, r);
            return Ok(r);
        }
        self.eval_bool_pol_inner(expr, t, negated)
    }

    fn eval_bool_pol_inner(
        &mut self,
        expr: &RExpr,
        t: usize,
        negated: bool,
    ) -> Result<BoolRes, EvalError> {
        match expr {
            RExpr::Un(UnOp::Not, x) => return self.eval_bool_pol(x, t, !negated),
            RExpr::Bin(BinOp::And, a, b) => {
                if !negated {
                    let ra = self.eval_bool_pol(a, t, false)?;
                    if !ra.val {
                        return Ok(ra);
                    }
                    let rb = self.eval_bool_pol(b, t, false)?;
                    return Ok(BoolRes {
                        val: rb.val,
                        of: ra.of || rb.of,
                    });
                } else {
                    let ra = self.eval_bool_pol(a, t, true)?;
                    if ra.val && (!self.env.no_overflow || !ra.of) {
                        return Ok(ra);
                    }
                    let rb = self.eval_bool_pol(b, t, true)?;
                    return Ok(BoolRes {
                        val: (ra.val && (!self.env.no_overflow || !ra.of))
                            || (rb.val && (!self.env.no_overflow || !rb.of)),
                        of: false,
                    });
                }
            }
            RExpr::Bin(BinOp::Or, a, b) => {
                if !negated {
                    let ra = self.eval_bool_pol(a, t, false)?;
                    if ra.val && (!self.env.no_overflow || !ra.of) {
                        return Ok(ra);
                    }
                    let rb = self.eval_bool_pol(b, t, false)?;
                    return Ok(BoolRes {
                        val: (ra.val && (!self.env.no_overflow || !ra.of))
                            || (rb.val && (!self.env.no_overflow || !rb.of)),
                        of: false,
                    });
                } else {
                    let ra = self.eval_bool_pol(a, t, true)?;
                    if !ra.val {
                        return Ok(ra);
                    }
                    let rb = self.eval_bool_pol(b, t, true)?;
                    return Ok(BoolRes {
                        val: rb.val,
                        of: ra.of || rb.of,
                    });
                }
            }
            RExpr::Bin(BinOp::Implies, a, b) => {
                if !negated {
                    let ra = self.eval_bool_pol(a, t, false)?;
                    if !ra.val || (self.env.no_overflow && ra.of) {
                        return Ok(BoolRes { val: true, of: false });
                    }
                    return self.eval_bool_pol(b, t, false);
                } else {
                    let ra = self.eval_bool_pol(a, t, false)?;
                    if !ra.val || (self.env.no_overflow && ra.of) {
                        return Ok(BoolRes { val: false, of: false });
                    }
                    return self.eval_bool_pol(b, t, true);
                }
            }
            RExpr::Block(items) => {
                if items.len() == 1 {
                    return self.eval_bool_pol(&items[0], t, negated);
                }
                if !negated {
                    let mut any_of = false;
                    for item in items {
                        let r = self.eval_bool_pol(item, t, false)?;
                        any_of |= r.of;
                        if !r.val {
                            return Ok(BoolRes { val: false, of: any_of });
                        }
                    }
                    return Ok(BoolRes { val: true, of: any_of });
                } else {
                    for item in items {
                        let r = self.eval_bool_pol(item, t, true)?;
                        if r.val && (!self.env.no_overflow || !r.of) {
                            return Ok(BoolRes { val: true, of: false });
                        }
                    }
                    return Ok(BoolRes { val: false, of: false });
                }
            }
            RExpr::Let(bs, b) => {
                let old_l = self.locals.len();
                let old_lazy = self.lazy.len();
                let old_lt = self.ltypes.len();
                let mut of = false;
                for (l, ex) in bs {
                    let lt = self.rty(ex).unwrap_or_else(Self::empty_ty);
                    if self.model.macro_locals.contains(l) {
                        self.lazy.push((*l, ex.clone()));
                    } else {
                        let ev = self.eval_val(ex, t, false)?;
                        of |= ev.of;
                        self.locals.push((*l, ev.val));
                    }
                    self.ltypes.push((*l, lt));
                }
                let res = self.eval_bool_pol(b, t, negated);
                self.locals.truncate(old_l);
                self.lazy.truncate(old_lazy);
                self.ltypes.truncate(old_lt);
                let mut res = res?;
                res.of |= of;
                return Ok(res);
            }
            RExpr::Quant(Quant::All, ds, b) if negated => {
                return self.eval_quant(Quant::Some, ds, b, t, true);
            }
            RExpr::Quant(Quant::Some, ds, b) if !negated => {
                return self.eval_quant(Quant::Some, ds, b, t, false);
            }
            _ => {}
        }
        let r = self.eval_val(expr, t, false)?;
        let b = match r.val {
            Value::Bool(b) => b,
            other => {
                return Err(EvalError::new(format!(
                    "expected formula, got {other:?} from {:.120}",
                    format!("{expr:?}")
                )))
            }
        };
        let eff_b = if self.env.no_overflow && r.of {
            false
        } else {
            b
        };
        Ok(BoolRes {
            val: if negated { !eff_b } else { eff_b },
            of: false,
        })
    }

    fn eval_val(
        &mut self,
        expr: &RExpr,
        t: usize,
        negated_body: bool,
    ) -> Result<EvalVal, EvalError> {
        let _ = negated_body;
        let st = self.st(t);
        match expr {
            RExpr::Sig(s) => Ok(EvalVal {
                val: Value::Rel(self.env.states[st].sigs[*s as usize].clone()),
                of: false,
            }),
            RExpr::Field(f) => Ok(EvalVal {
                val: Value::Rel(self.env.states[st].fields[*f as usize].clone()),
                of: false,
            }),
            RExpr::Local(l) => {
                if let Some(lz) = self.lazy_get(*l) {
                    return self.eval_val(&lz, t, false);
                }
                let v = self.local_get(*l).cloned().ok_or_else(|| {
                    let lname = self
                        .model
                        .locals
                        .get(*l as usize)
                        .map_or("?", String::as_str);
                    EvalError::new(format!("unbound local variable '{lname}' ({l})"))
                })?;
                Ok(EvalVal { val: v, of: false })
            }
            RExpr::Const(c) => match c {
                Const::Univ => Ok(EvalVal {
                    val: Value::Rel(self.env.states[st].sigs[alloy_core::sema::SIG_UNIV as usize].clone()),
                    of: false,
                }),
                Const::None => Ok(EvalVal {
                    val: Value::Rel(RelVal::empty(1)),
                    of: false,
                }),
                Const::Iden => Ok(EvalVal {
                    val: Value::Rel(self.env.states[st].iden.clone()),
                    of: false,
                }),
                Const::SigInt => Ok(EvalVal {
                    val: Value::Rel(self.env.states[st].sigs[SIG_INT as usize].clone()),
                    of: false,
                }),
                Const::SigString => Ok(EvalVal {
                    val: Value::Rel(self.env.states[st].sigs[alloy_core::sema::SIG_STRING as usize].clone()),
                    of: false,
                }),
                Const::IntMin => Ok(EvalVal {
                    val: Value::Int(self.env.universe.min_int),
                    of: false,
                }),
                Const::IntMax => Ok(EvalVal {
                    val: Value::Int(self.env.universe.max_int),
                    of: false,
                }),
                Const::IntNext => Ok(EvalVal {
                    val: Value::Rel(self.env.states[st].int_next.clone()),
                    of: false,
                }),
                Const::This => Err(EvalError::new("bare `this` constant during evaluation")),
            },
            RExpr::Num(n) => {
                let (w, _) = wrap_int(*n as i64, self.env.bitwidth);
                Ok(EvalVal { val: Value::Int(w), of: false })
            }
            RExpr::Str(s) => {
                let r = match self.env.universe.str_atom.get(s) {
                    Some(&a) => RelVal::singleton(1, vec![a]),
                    None => RelVal::empty(1),
                };
                Ok(EvalVal { val: Value::Rel(r), of: false })
            }
            RExpr::Un(op, x) => self.eval_un(*op, x, t),
            RExpr::Bin(op, a, b) => self.eval_bin(*op, a, b, t),
            RExpr::Ite(c, a, b) => {
                let cond = self.eval_bool_pol(c, t, false)?;
                let mut res = if cond.val {
                    self.eval_val(a, t, false)?
                } else {
                    self.eval_val(b, t, false)?
                };
                res.of |= cond.of;
                Ok(res)
            }
            RExpr::Let(bs, b) => {
                let old_l = self.locals.len();
                let old_lazy = self.lazy.len();
                let old_lt = self.ltypes.len();
                let mut of = false;
                for (l, ex) in bs {
                    let lt = self.rty(ex).unwrap_or_else(Self::empty_ty);
                    if self.model.macro_locals.contains(l) {
                        self.lazy.push((*l, ex.clone()));
                    } else {
                        let ev = self.eval_val(ex, t, false)?;
                        of |= ev.of;
                        self.locals.push((*l, ev.val));
                    }
                    self.ltypes.push((*l, lt));
                }
                let res = self.eval_val(b, t, false);
                self.locals.truncate(old_l);
                self.lazy.truncate(old_lazy);
                self.ltypes.truncate(old_lt);
                let mut res = res?;
                res.of |= of;
                Ok(res)
            }
            RExpr::Call(fid, args) => self.eval_call(*fid, args, t),
            RExpr::Block(items) if items.len() == 1 => self.eval_val(&items[0], t, false),
            RExpr::Block(items) => {
                let mut any_of = false;
                for item in items {
                    let r = self.eval_bool_pol(item, t, false)?;
                    any_of |= r.of;
                    if !r.val {
                        return Ok(EvalVal {
                            val: Value::Bool(false),
                            of: any_of,
                        });
                    }
                }
                Ok(EvalVal {
                    val: Value::Bool(true),
                    of: any_of,
                })
            }
            RExpr::Disj(args) => {
                let resolved = self.resolve_disj(args)?;
                let mut seen = RelVal::empty(1);
                let mut first = true;
                let mut any_of = false;
                for arg in &resolved {
                    let (r, of) = self.eval_rel(arg, t)?;
                    any_of |= of;
                    if first {
                        seen = r;
                        first = false;
                    } else {
                        if !seen.is_disjoint(&r) {
                            return Ok(EvalVal {
                                val: Value::Bool(false),
                                of: any_of,
                            });
                        }
                        seen = seen.union(&r);
                    }
                }
                Ok(EvalVal {
                    val: Value::Bool(true),
                    of: any_of,
                })
            }
            RExpr::TotalOrder(args) => self.eval_total_order(args, t),
            RExpr::Quant(q, ds, body) => match q {
                Quant::Sum => self.eval_sum(ds, body, t),
                _ => {
                    let br = self.eval_quant(*q, ds, body, t, false)?;
                    Ok(EvalVal { val: Value::Bool(br.val), of: br.of })
                }
            },
            RExpr::Compr(ds, body) => self.eval_compr(ds, body, t),
            RExpr::Choice(c) if c.len() == 1 => self.eval_val(&c[0], t, false),
            RExpr::Choice(_) => {
                let r = self.resolve(expr, &Exp::Any)?;
                if is_choice(&r) {
                    return Err(EvalError::new(format!(
                        "ambiguous Choice expression: {:.160}",
                        format!("{r:?}")
                    )));
                }
                let res = self.eval_val(&r, t, false);
                self.temp_memo.clear();
                res
            }
        }
    }

    fn eval_un(&mut self, op: UnOp, x: &RExpr, t: usize) -> Result<EvalVal, EvalError> {
        let st = self.st(t);
        match op {
            UnOp::Not => {
                let r = self.eval_bool_pol(x, t, false)?;
                Ok(EvalVal { val: Value::Bool(!r.val), of: r.of })
            }
            UnOp::No | UnOp::Some | UnOp::Lone | UnOp::One => {
                let (r, of) = self.eval_rel(x, t)?;
                let b = match op {
                    UnOp::No => r.is_empty(),
                    UnOp::Some => !r.is_empty(),
                    UnOp::Lone => r.len() <= 1,
                    UnOp::One => r.len() == 1,
                    _ => unreachable!(),
                };
                Ok(EvalVal {
                    val: Value::Bool(if self.env.no_overflow && of { false } else { b }),
                    of,
                })
            }
            UnOp::Set | UnOp::ExactlyOf => {
                let (r, of) = self.eval_rel(x, t)?;
                Ok(EvalVal { val: Value::Rel(r), of })
            }
            UnOp::Seq => {
                let (r, of) = self.eval_rel(x, t)?;
                let seq_ints = &self.env.states[st].sigs[SIG_SEQINT as usize];
                Ok(EvalVal {
                    val: Value::Rel(seq_ints.product(&r)),
                    of,
                })
            }
            UnOp::Card => {
                let (r, of) = self.eval_rel(x, t)?;
                let (w, cof) = wrap_int(r.len() as i64, self.env.bitwidth);
                Ok(EvalVal {
                    val: Value::Int(w),
                    of: of || cof,
                })
            }
            UnOp::Transpose => {
                let (r, of) = self.eval_rel(x, t)?;
                Ok(EvalVal {
                    val: Value::Rel(r.transpose()?),
                    of,
                })
            }
            UnOp::Closure => {
                let (r, of) = self.eval_rel(x, t)?;
                Ok(EvalVal {
                    val: Value::Rel(r.closure()?),
                    of,
                })
            }
            UnOp::ReflClosure => {
                let (r, of) = self.eval_rel(x, t)?;
                let iden = &self.env.states[st].iden;
                Ok(EvalVal {
                    val: Value::Rel(r.refl_closure(iden)?),
                    of,
                })
            }
            UnOp::IntCast => {
                let (i, of) = self.eval_int(x, t)?;
                Ok(EvalVal { val: Value::Int(i), of })
            }
            UnOp::SigInt => self.eval_val(x, t, false),
            UnOp::Neg => {
                let (i, of) = self.eval_int(x, t)?;
                let (w, nof) = wrap_int(-(i as i64), self.env.bitwidth);
                Ok(EvalVal {
                    val: Value::Int(w),
                    of: of || nof,
                })
            }
            UnOp::Prime | UnOp::After => {
                let nt = self.horizon.step_next(t);
                self.eval_val(x, nt, false)
            }
            UnOp::Always => {
                let seq = self.horizon.future_seq(t);
                let mut any_of = false;
                for u in seq {
                    let r = self.eval_bool_pol(x, u, false)?;
                    any_of |= r.of;
                    if !r.val {
                        return Ok(EvalVal { val: Value::Bool(false), of: any_of });
                    }
                }
                Ok(EvalVal { val: Value::Bool(true), of: any_of })
            }
            UnOp::Eventually => {
                let seq = self.horizon.future_seq(t);
                let mut any_of = false;
                for u in seq {
                    let r = self.eval_bool_pol(x, u, false)?;
                    any_of |= r.of;
                    if r.val {
                        return Ok(EvalVal { val: Value::Bool(true), of: r.of });
                    }
                }
                Ok(EvalVal { val: Value::Bool(false), of: any_of })
            }
            UnOp::Before => {
                if t == 0 {
                    return Ok(EvalVal { val: Value::Bool(false), of: false });
                }
                let r = self.eval_bool_pol(x, t - 1, false)?;
                Ok(EvalVal { val: Value::Bool(r.val), of: r.of })
            }
            UnOp::Once => {
                let mut any_of = false;
                for j in (0..=t).rev() {
                    let r = self.eval_bool_pol(x, j, false)?;
                    any_of |= r.of;
                    if r.val {
                        return Ok(EvalVal { val: Value::Bool(true), of: r.of });
                    }
                }
                Ok(EvalVal { val: Value::Bool(false), of: any_of })
            }
            UnOp::Historically => {
                let mut any_of = false;
                for j in (0..=t).rev() {
                    let r = self.eval_bool_pol(x, j, false)?;
                    any_of |= r.of;
                    if !r.val {
                        return Ok(EvalVal { val: Value::Bool(false), of: any_of });
                    }
                }
                Ok(EvalVal { val: Value::Bool(true), of: any_of })
            }
        }
    }

    fn eval_bin(
        &mut self,
        op: BinOp,
        a: &RExpr,
        b: &RExpr,
        t: usize,
    ) -> Result<EvalVal, EvalError> {
        let (ra, rb);
        let mut resolved_choice = false;
        let (a, b) = match op {
            BinOp::Join if is_choice(a) || is_choice(b) => {
                resolved_choice = true;
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
                if is_choice(a) || is_choice(b) =>
            {
                resolved_choice = true;
                (ra, rb) = self.resolve_pair(a, b)?;
                (&ra, &rb)
            }
            BinOp::DomainRestrict if is_choice(b) => {
                resolved_choice = true;
                (ra, rb) = self.resolve_restrict(a, b, true)?;
                (&ra, &rb)
            }
            BinOp::RangeRestrict if is_choice(a) => {
                resolved_choice = true;
                (ra, rb) = self.resolve_restrict(a, b, false)?;
                (&ra, &rb)
            }
            _ => (a, b),
        };
        let res = self.eval_bin_inner(op, a, b, t);
        if resolved_choice {
            self.temp_memo.clear();
        }
        res
    }

    fn eval_bin_inner(
        &mut self,
        op: BinOp,
        a: &RExpr,
        b: &RExpr,
        t: usize,
    ) -> Result<EvalVal, EvalError> {
        match op {
            BinOp::And | BinOp::Or => {
                let r = self.eval_bool_pol_inner(
                    &RExpr::Bin(op, Box::new(a.clone()), Box::new(b.clone())),
                    t,
                    false,
                )?;
                Ok(EvalVal { val: Value::Bool(r.val), of: r.of })
            }
            BinOp::Implies => {
                let ra = self.eval_bool_pol(a, t, false)?;
                if !ra.val || (self.env.no_overflow && ra.of) {
                    return Ok(EvalVal { val: Value::Bool(true), of: false });
                }
                let rb = self.eval_bool_pol(b, t, false)?;
                Ok(EvalVal { val: Value::Bool(rb.val), of: rb.of })
            }
            BinOp::Iff => {
                let ra = self.eval_bool_pol(a, t, false)?;
                let rb = self.eval_bool_pol(b, t, false)?;
                let va = ra.val && (!self.env.no_overflow || !ra.of);
                let vb = rb.val && (!self.env.no_overflow || !rb.of);
                Ok(EvalVal { val: Value::Bool(va == vb), of: false })
            }
            BinOp::Until => {
                let seq = self.horizon.future_seq(t);
                let mut any_of = false;
                for &u in &seq {
                    let rb = self.eval_bool_pol(b, u, false)?;
                    any_of |= rb.of;
                    if rb.val {
                        return Ok(EvalVal { val: Value::Bool(true), of: any_of });
                    }
                    let ra = self.eval_bool_pol(a, u, false)?;
                    any_of |= ra.of;
                    if !ra.val {
                        return Ok(EvalVal { val: Value::Bool(false), of: any_of });
                    }
                }
                Ok(EvalVal { val: Value::Bool(false), of: any_of })
            }
            BinOp::Releases => {
                let seq = self.horizon.future_seq(t);
                let mut any_of = false;
                for &u in &seq {
                    let rb = self.eval_bool_pol(b, u, false)?;
                    any_of |= rb.of;
                    if !rb.val {
                        return Ok(EvalVal { val: Value::Bool(false), of: any_of });
                    }
                    let ra = self.eval_bool_pol(a, u, false)?;
                    any_of |= ra.of;
                    if ra.val {
                        return Ok(EvalVal { val: Value::Bool(true), of: any_of });
                    }
                }
                Ok(EvalVal { val: Value::Bool(true), of: any_of })
            }
            BinOp::Since => {
                let mut any_of = false;
                for j in (0..=t).rev() {
                    let rb = self.eval_bool_pol(b, j, false)?;
                    any_of |= rb.of;
                    if rb.val {
                        return Ok(EvalVal { val: Value::Bool(true), of: any_of });
                    }
                    let ra = self.eval_bool_pol(a, j, false)?;
                    any_of |= ra.of;
                    if !ra.val {
                        return Ok(EvalVal { val: Value::Bool(false), of: any_of });
                    }
                }
                Ok(EvalVal { val: Value::Bool(false), of: any_of })
            }
            BinOp::Triggered => {
                let mut any_of = false;
                for j in (0..=t).rev() {
                    let rb = self.eval_bool_pol(b, j, false)?;
                    any_of |= rb.of;
                    if !rb.val {
                        return Ok(EvalVal { val: Value::Bool(false), of: any_of });
                    }
                    let ra = self.eval_bool_pol(a, j, false)?;
                    any_of |= ra.of;
                    if ra.val {
                        return Ok(EvalVal { val: Value::Bool(true), of: any_of });
                    }
                }
                Ok(EvalVal { val: Value::Bool(true), of: any_of })
            }
            BinOp::Equals => {
                let va = self.eval_val(a, t, false)?;
                let vb = self.eval_val(b, t, false)?;
                let of = va.of || vb.of;
                let eq = match (va.val, vb.val) {
                    (Value::Int(x), Value::Int(y)) => x == y,
                    (x, y) => self.val_to_rel(x)? == self.val_to_rel(y)?,
                };
                Ok(EvalVal {
                    val: Value::Bool(if self.env.no_overflow && of { false } else { eq }),
                    of,
                })
            }
            BinOp::In => {
                let (r, of_a) = self.eval_rel(a, t)?;
                let (ok, of_b) = self.eval_is_in(&r, b, t)?;
                let of = of_a || of_b;
                Ok(EvalVal {
                    val: Value::Bool(if self.env.no_overflow && of { false } else { ok }),
                    of,
                })
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let (ia, oa) = self.eval_int(a, t)?;
                let (ib, ob) = self.eval_int(b, t)?;
                let of = oa || ob;
                let cmp = match op {
                    BinOp::Lt => ia < ib,
                    BinOp::Le => ia <= ib,
                    BinOp::Gt => ia > ib,
                    BinOp::Ge => ia >= ib,
                    _ => unreachable!(),
                };
                Ok(EvalVal {
                    val: Value::Bool(if self.env.no_overflow && of { false } else { cmp }),
                    of,
                })
            }
            BinOp::IntPlus | BinOp::IntMinus | BinOp::Mul | BinOp::Div | BinOp::Rem | BinOp::Shl | BinOp::Shr | BinOp::Sha => {
                let (ia, oa) = self.eval_int(a, t)?;
                let (ib, ob) = self.eval_int(b, t)?;
                let bw = self.env.bitwidth;
                let (res, op_of) = match op {
                    BinOp::IntPlus => wrap_int(ia as i64 + ib as i64, bw),
                    BinOp::IntMinus => wrap_int(ia as i64 - ib as i64, bw),
                    BinOp::Mul => wrap_int(ia as i64 * ib as i64, bw),
                    BinOp::Div => int_div(ia, ib, self.env.universe.min_int),
                    BinOp::Rem => int_rem(ia, ib, self.env.universe.min_int),
                    BinOp::Shl => int_shl(ia, ib, bw),
                    BinOp::Shr => int_shr(ia, ib, bw, false),
                    BinOp::Sha => int_shr(ia, ib, bw, true),
                    _ => unreachable!(),
                };
                Ok(EvalVal {
                    val: Value::Int(res),
                    of: oa || ob || op_of,
                })
            }
            BinOp::Plus => {
                let (ra, oa) = self.eval_rel(a, t)?;
                let (rb, ob) = self.eval_rel(b, t)?;
                Ok(EvalVal { val: Value::Rel(ra.union(&rb)), of: oa || ob })
            }
            BinOp::Minus => {
                if let (RExpr::Num(0), RExpr::Num(m)) = (a, b) {
                    if *m == self.env.universe.max_int + 1 {
                        return Ok(EvalVal {
                            val: Value::Int(self.env.universe.min_int),
                            of: false,
                        });
                    }
                }
                let (ra, oa) = self.eval_rel(a, t)?;
                let (rb, ob) = self.eval_rel(b, t)?;
                Ok(EvalVal { val: Value::Rel(ra.diff(&rb)), of: oa || ob })
            }
            BinOp::Intersect => {
                let (ra, oa) = self.eval_rel(a, t)?;
                let (rb, ob) = self.eval_rel(b, t)?;
                Ok(EvalVal { val: Value::Rel(ra.intersect(&rb)), of: oa || ob })
            }
            BinOp::Override => {
                let (ra, oa) = self.eval_rel(a, t)?;
                let (rb, ob) = self.eval_rel(b, t)?;
                Ok(EvalVal { val: Value::Rel(ra.override_(&rb)), of: oa || ob })
            }
            BinOp::Arrow(..) => {
                let (ra, oa) = self.eval_rel(a, t)?;
                let (rb, ob) = self.eval_rel(b, t)?;
                Ok(EvalVal { val: Value::Rel(ra.product(&rb)), of: oa || ob })
            }
            BinOp::Join => {
                let (ra, oa) = self.eval_rel(a, t)?;
                let (rb, ob) = self.eval_rel(b, t)?;
                let j = ra.join(&rb).map_err(|e| {
                    EvalError::new(format!("{} (lhs={a:?}, rhs={b:?})", e.message))
                })?;
                Ok(EvalVal { val: Value::Rel(j), of: oa || ob })
            }
            BinOp::DomainRestrict => {
                let (ra, oa) = self.eval_rel(a, t)?;
                let (rb, ob) = self.eval_rel(b, t)?;
                Ok(EvalVal {
                    val: Value::Rel(RelVal::domain_restrict(&ra, &rb)),
                    of: oa || ob,
                })
            }
            BinOp::RangeRestrict => {
                let (ra, oa) = self.eval_rel(a, t)?;
                let (rb, ob) = self.eval_rel(b, t)?;
                Ok(EvalVal {
                    val: Value::Rel(ra.range_restrict(&rb)),
                    of: oa || ob,
                })
            }
        }
    }

    fn eval_call(&mut self, fid: FuncId, args: &[RExpr], t: usize) -> Result<EvalVal, EvalError> {
        let func = &self.model.funcs[fid as usize];
        let n = func.params.len();
        if n == 0 && !expr_is_temporal(self.model, &func.body) {
            if let Some(v) = self.zero_arg_cache.get(&(fid, self.st(t))) {
                return Ok(v.clone());
            }
        }
        let mut rem_rec = self.env.unrolls;
        for &cf in &self.call_stack {
            if cf == fid {
                if rem_rec < 0 {
                    return Err(EvalError::new(format!(
                        "{} cannot call itself recursively!",
                        func.label
                    )));
                }
                if rem_rec == 0 {
                    if func.is_pred {
                        return Ok(EvalVal { val: Value::Bool(false), of: false });
                    }
                    if let Some(ref ret) = func.ret {
                        if java_small_int(ret, &mut Vec::new())
                            || matches!(ret, RExpr::Sig(SIG_INT) | RExpr::Const(Const::SigInt))
                        {
                            return Ok(EvalVal { val: Value::Int(0), of: false });
                        }
                        let ar = expr_arity(self.model, ret);
                        return Ok(EvalVal { val: Value::Rel(RelVal::empty(ar)), of: false });
                    }
                    return Ok(EvalVal { val: Value::Rel(RelVal::empty(1)), of: false });
                }
                rem_rec -= 1;
            }
        }
        if args.len() != n {
            return Err(EvalError::new("call arity mismatch"));
        }
        let params = func.params.clone();
        let mut new_locals = Vec::with_capacity(n);
        let mut new_ltypes = Vec::with_capacity(n);
        let mut arg_of = false;
        for (i, (pl, pb)) in params.iter().enumerate() {
            let arg = if is_choice(&args[i]) {
                let exp = self.rty_with(pb, &new_ltypes).map_or(Exp::Any, Exp::Same);
                self.resolve(&args[i], &exp)?
            } else {
                args[i].clone()
            };
            let arg_ty = self.rty(&arg).unwrap_or_else(Self::empty_ty);
            let (rv, of) = self.eval_rel(&arg, t)?;
            arg_of |= of;
            new_locals.push((*pl, Value::Rel(rv)));
            new_ltypes.push((*pl, arg_ty));
        }
        let body = &self.model.funcs[fid as usize].body;
        let old_locals = std::mem::replace(&mut self.locals, new_locals);
        let old_ltypes = std::mem::replace(&mut self.ltypes, new_ltypes);
        let old_lazy = std::mem::take(&mut self.lazy);
        self.call_stack.push(fid);
        let res = self.eval_val(body, t, false);
        self.locals = old_locals;
        self.ltypes = old_ltypes;
        self.lazy = old_lazy;
        self.call_stack.pop();
        let mut res = res?;
        res.of |= arg_of;
        if n == 0 && !expr_is_temporal(self.model, &func.body) {
            self.zero_arg_cache.insert((fid, self.st(t)), res.clone());
        }
        Ok(res)
    }

    fn eval_total_order(&mut self, args: &[RExpr], t: usize) -> Result<EvalVal, EvalError> {
        let resolved = self.resolve_total_order(args)?;
        if resolved.len() != 3 {
            return Err(EvalError::new("totalOrder expects 3 arguments"));
        }
        let (elem, o0) = self.eval_rel(&resolved[0], t)?;
        let (first, o1) = self.eval_rel(&resolved[1], t)?;
        let (next, o2) = self.eval_rel(&resolved[2], t)?;
        let of = o0 || o1 || o2;
        if elem.arity != 1 || first.arity != 1 || next.arity != 2 {
            return Ok(EvalVal { val: Value::Bool(false), of });
        }
        let ok = check_total_order(&elem, &first, &next);
        Ok(EvalVal {
            val: Value::Bool(if self.env.no_overflow && of { false } else { ok }),
            of,
        })
    }

    pub(crate) fn eval_is_in(
        &mut self,
        r: &RelVal,
        rhs: &RExpr,
        t: usize,
    ) -> Result<(bool, bool), EvalError> {
        if is_mult_arrow(rhs) {
            return self.eval_is_in_binary(r, rhs, t);
        }
        let (m, inner) = decl_mult(rhs);
        let (b, of) = self.eval_rel(inner, t)?;
        let ok = match m {
            Some(UnOp::ExactlyOf) => r == &b,
            Some(UnOp::One) => r.len() == 1 && r.is_subset_of(&b),
            Some(UnOp::Lone) => r.len() <= 1 && r.is_subset_of(&b),
            Some(UnOp::Some) => !r.is_empty() && r.is_subset_of(&b),
            _ => r.is_subset_of(&b),
        };
        Ok((ok, of))
    }

    fn eval_is_in_binary(
        &mut self,
        r: &RelVal,
        ab: &RExpr,
        t: usize,
    ) -> Result<(bool, bool), EvalError> {
        let (lm, rm, left, right, isseq) = match ab {
            RExpr::Bin(BinOp::Arrow(l, rr), x, y) => {
                let (x, y) = self.resolve_pair(x, y)?;
                (*l, *rr, x, y, false)
            }
            RExpr::Un(UnOp::Seq, y) => (
                Mult::Set,
                Mult::Lone,
                RExpr::Sig(SIG_SEQINT),
                (**y).clone(),
                true,
            ),
            _ => unreachable!(),
        };
        let (a, oa) = self.eval_rel(&left, t)?;
        let (b, ob) = self.eval_rel(&right, t)?;
        let mut of = oa || ob;
        if r.arity != a.arity + b.arity {
            return Ok((false, of));
        }
        let aa = a.arity as usize;
        // Partition every tuple in r into prefix (len aa) and suffix (len bb); check prefix in a, suffix in b, and group maps.
        let mut by_prefix: HashMap<&[AtomIdx], Vec<Vec<AtomIdx>>> = HashMap::new();
        let mut by_suffix: HashMap<&[AtomIdx], Vec<Vec<AtomIdx>>> = HashMap::new();
        for tup in &r.tuples {
            let (p, s) = tup.split_at(aa);
            by_prefix.entry(p).or_default().push(s.to_vec());
            by_suffix.entry(s).or_default().push(p.to_vec());
        }
        // Subset check r <= a -> b (prefix in a, suffix in b)
        for p in by_prefix.keys() {
            if !a.contains(p) {
                return Ok((false, of));
            }
        }
        for s in by_suffix.keys() {
            if !b.contains(s) {
                return Ok((false, of));
            }
        }
        // Right multiplicity (rm) over each tuple `p` in `a`:
        for p in &a.tuples {
            let matches = by_prefix
                .get(p.as_slice())
                .map_or_else(Vec::new, |v| v.clone());
            let sub = RelVal::from_tuples(b.arity, matches);
            let cnt_ok = mult_ok(rm, sub.len());
            if !cnt_ok {
                return Ok((false, of));
            }
            if is_mult_arrow(&right) || !matches!(decl_mult(&right).0, None | Some(UnOp::Set)) {
                let (ok_r, o_r) = self.eval_is_in(&sub, &right, t)?;
                of |= o_r;
                if !ok_r {
                    return Ok((false, of));
                }
            }
        }
        // Left multiplicity (lm) over each tuple `s` in `b`:
        for s in &b.tuples {
            let matches = by_suffix
                .get(s.as_slice())
                .map_or_else(Vec::new, |v| v.clone());
            let sub = RelVal::from_tuples(a.arity, matches);
            let cnt_ok = mult_ok(lm, sub.len());
            if !cnt_ok {
                return Ok((false, of));
            }
            if is_mult_arrow(&left) || !matches!(decl_mult(&left).0, None | Some(UnOp::Set)) {
                let (ok_l, o_l) = self.eval_is_in(&sub, &left, t)?;
                of |= o_l;
                if !ok_l {
                    return Ok((false, of));
                }
            }
        }
        // Seq contiguity check: keys must form contiguous 0..k-1
        if isseq && !r.tuples.is_empty() {
            let indices: BTreeSet<i32> = by_prefix
                .keys()
                .filter_map(|p| self.env.universe.int_val[p[0].0 as usize])
                .collect();
            if indices.len() != by_prefix.len() {
                return Ok((false, of));
            }
            for k in 0..indices.len() as i32 {
                if !indices.contains(&k) {
                    return Ok((false, of));
                }
            }
        }
        Ok((true, of))
    }

    fn skolem_candidates(&self, var_name: &str, arity: u32) -> Vec<RelVal> {
        let mut exact = Vec::new();
        let mut suffix = Vec::new();
        let caller = self
            .call_stack
            .last()
            .map(|&f| {
                let l = &self.model.funcs[f as usize].label;
                l.rsplit('/').next().unwrap_or(l)
            })
            .unwrap_or("");
        for (sk_name, raw) in &self.env.skolems {
            if !raw.is_empty() && raw[0].len() != arity as usize {
                continue;
            }
            let base = sk_name.trim_start_matches('$').trim_end_matches('"').trim_end_matches('\'');
            let want_exact = format!("{caller}_{var_name}");
            if base == want_exact || base == var_name {
                exact.push(RelVal::from_tuples(arity, raw.clone()));
            } else if base.ends_with(&format!("_{var_name}")) || base.contains(&format!("_{var_name}'")) {
                suffix.push(RelVal::from_tuples(arity, raw.clone()));
            }
        }
        exact.extend(suffix);
        exact
    }

    fn eval_compr(
        &mut self,
        decls: &[RDecl],
        body: &RExpr,
        t: usize,
    ) -> Result<EvalVal, EvalError> {
        let flat = self.flatten_decls(decls, t)?;
        let mut out_tuples = Vec::new();
        let mut any_of = flat.of;
        let total_arity: u32 = flat.items.iter().map(|i| i.arity).sum();
        let mut tuple_acc = Vec::with_capacity(total_arity as usize);
        self.compr_rec(&flat.items, 0, body, t, &mut tuple_acc, &mut out_tuples, &mut any_of)?;
        Ok(EvalVal {
            val: Value::Rel(RelVal::from_tuples(total_arity, out_tuples)),
            of: any_of,
        })
    }

    fn compr_rec(
        &mut self,
        items: &[DeclVar],
        idx: usize,
        body: &RExpr,
        t: usize,
        acc: &mut Vec<AtomIdx>,
        out: &mut Vec<Vec<AtomIdx>>,
        any_of: &mut bool,
    ) -> Result<(), EvalError> {
        if idx == items.len() {
            let br = self.eval_bool_pol(body, t, false)?;
            *any_of |= br.of;
            if br.val && (!self.env.no_overflow || !br.of) {
                out.push(acc.clone());
            }
            return Ok(());
        }
        let d = &items[idx];
        let chosen = self.resolve_decl_bound(d, t)?;
        *any_of |= chosen.1;
        let bound_expr = d.bound_expr.clone();
        let vals = self.enumerate_domain(&chosen.0, &bound_expr, d.mult, d.is_unary_one, t)?;
        let d_ty = self.rty(&d.inner_expr).unwrap_or_else(Self::empty_ty);
        let old_l = self.locals.len();
        let old_lt = self.ltypes.len();
        let old_len = acc.len();
        for val in vals {
            if d.group_start < idx && !self.disj_ok(d.group_start, idx, &val) {
                continue;
            }
            if val.len() == 1 {
                acc.extend_from_slice(&val.tuples[0]);
            }
            self.locals.push((d.var, Value::Rel(val)));
            self.ltypes.push((d.var, d_ty.clone()));
            self.compr_rec(items, idx + 1, body, t, acc, out, any_of)?;
            self.locals.truncate(old_l);
            self.ltypes.truncate(old_lt);
            acc.truncate(old_len);
        }
        Ok(())
    }

    fn eval_sum(
        &mut self,
        decls: &[RDecl],
        body: &RExpr,
        t: usize,
    ) -> Result<EvalVal, EvalError> {
        let flat = self.flatten_decls(decls, t)?;
        let mut vals = Vec::new();
        let mut any_of = flat.of;
        self.sum_rec(&flat.items, 0, body, t, &mut vals, &mut any_of)?;
        let (sum, sof) = sum_slice(&vals, self.env.bitwidth);
        Ok(EvalVal {
            val: Value::Int(sum),
            of: any_of || sof,
        })
    }

    fn sum_rec(
        &mut self,
        items: &[DeclVar],
        idx: usize,
        body: &RExpr,
        t: usize,
        vals: &mut Vec<i32>,
        any_of: &mut bool,
    ) -> Result<(), EvalError> {
        if idx == items.len() {
            let (iv, iof) = self.eval_int(body, t)?;
            *any_of |= iof;
            vals.push(iv);
            return Ok(());
        }
        let d = &items[idx];
        let (domain, bof) = self.resolve_decl_bound(d, t)?;
        *any_of |= bof;
        let bound_expr = d.bound_expr.clone();
        let cands = self.enumerate_domain(&domain, &bound_expr, d.mult, d.is_unary_one, t)?;
        let d_ty = self.rty(&d.inner_expr).unwrap_or_else(Self::empty_ty);
        let old_l = self.locals.len();
        let old_lt = self.ltypes.len();
        for val in cands {
            if d.group_start < idx && !self.disj_ok(d.group_start, idx, &val) {
                continue;
            }
            self.locals.push((d.var, Value::Rel(val)));
            self.ltypes.push((d.var, d_ty.clone()));
            self.sum_rec(items, idx + 1, body, t, vals, any_of)?;
            self.locals.truncate(old_l);
            self.ltypes.truncate(old_lt);
        }
        Ok(())
    }

    fn eval_quant(
        &mut self,
        q: Quant,
        decls: &[RDecl],
        body: &RExpr,
        t: usize,
        negated_body: bool,
    ) -> Result<BoolRes, EvalError> {
        let flat = self.flatten_decls(decls, t)?;
        match q {
            Quant::All => {
                let mut any_of = flat.of;
                let ok = self.all_rec(&flat.items, 0, body, t, &mut any_of)?;
                Ok(BoolRes {
                    val: ok,
                    of: if self.env.no_overflow { false } else { any_of },
                })
            }
            Quant::Some => {
                let mut any_of = flat.of;
                let ok = self.some_rec(&flat.items, 0, body, t, negated_body, &mut any_of)?;
                Ok(BoolRes { val: ok, of: false })
            }
            Quant::No => {
                let mut any_of = flat.of;
                let some_ok = self.some_rec(&flat.items, 0, body, t, false, &mut any_of)?;
                Ok(BoolRes { val: !some_ok, of: false })
            }
            Quant::One | Quant::Lone => {
                let mut count = 0usize;
                let mut any_of = flat.of;
                self.count_rec(&flat.items, 0, body, t, &mut count, 2, &mut any_of)?;
                let ok = if q == Quant::One { count == 1 } else { count <= 1 };
                Ok(BoolRes {
                    val: if self.env.no_overflow && any_of { false } else { ok },
                    of: any_of,
                })
            }
            Quant::Sum => unreachable!(),
        }
    }

    fn flatten_decls(&mut self, decls: &[RDecl], _t: usize) -> Result<FlatDecls, EvalError> {
        let mut items = Vec::new();
        for d in decls {
            let (m, inner) = decl_mult(&d.bound);
            let inner = if is_choice(inner) {
                self.resolve(inner, &Exp::Any)?
            } else {
                inner.clone()
            };
            let arity = expr_arity(self.model, &inner);
            let is_unary_one = arity == 1 && matches!(m, None | Some(UnOp::One));
            let group_start = items.len();
            for &var in &d.vars {
                items.push(DeclVar {
                    var,
                    disjoint: d.disjoint,
                    group_start: if d.disjoint { group_start } else { usize::MAX },
                    bound_expr: d.bound.clone(),
                    inner_expr: inner.clone(),
                    mult: m,
                    arity,
                    is_unary_one,
                });
            }
        }
        Ok(FlatDecls { items, of: false })
    }

    fn resolve_decl_bound(&mut self, d: &DeclVar, t: usize) -> Result<(RelVal, bool), EvalError> {
        self.eval_rel(&d.inner_expr, t)
    }

    fn disj_ok(&self, group_start: usize, cur_idx: usize, cand: &RelVal) -> bool {
        let n_prev = cur_idx - group_start;
        let len = self.locals.len();
        for i in (len - n_prev)..len {
            if let Value::Rel(prev) = &self.locals[i].1 {
                if !prev.is_disjoint(cand) {
                    return false;
                }
            }
        }
        true
    }

    fn some_rec(
        &mut self,
        items: &[DeclVar],
        idx: usize,
        body: &RExpr,
        t: usize,
        negated_body: bool,
        any_of: &mut bool,
    ) -> Result<bool, EvalError> {
        if idx == items.len() {
            let br = self.eval_bool_pol(body, t, negated_body)?;
            return Ok(br.val && (!self.env.no_overflow || !br.of));
        }
        let d = items[idx].clone();
        let (domain, bof) = self.resolve_decl_bound(&d, t)?;
        *any_of |= bof;
        let var_name = self.model.locals.get(d.var as usize).map_or("", String::as_str).to_string();

        // Sound skolem witness fast-path: always validate cand via eval_is_in + disj_ok + body!
        let d_ty = self.rty(&d.inner_expr).unwrap_or_else(Self::empty_ty);
        let old_l = self.locals.len();
        let old_lt = self.ltypes.len();
        if !self.env.skolems.is_empty() {
            for cand in self.skolem_candidates(&var_name, d.arity) {
                if d.group_start < idx && !self.disj_ok(d.group_start, idx, &cand) {
                    continue;
                }
                let (in_ok, in_of) = if d.is_unary_one {
                    (cand.len() == 1 && cand.is_subset_of(&domain), false)
                } else {
                    self.eval_is_in(&cand, &d.bound_expr, t)?
                };
                if in_ok && (!self.env.no_overflow || !in_of) {
                    self.locals.push((d.var, Value::Rel(cand)));
                    self.ltypes.push((d.var, d_ty.clone()));
                    let res = self.some_rec(items, idx + 1, body, t, negated_body, any_of);
                    self.locals.truncate(old_l);
                    self.ltypes.truncate(old_lt);
                    if res? {
                        return Ok(true);
                    }
                }
            }
        }

        // Complete fallback enumeration
        let cands = self.enumerate_domain(&domain, &d.bound_expr, d.mult, d.is_unary_one, t)?;
        for cand in cands {
            if d.group_start < idx && !self.disj_ok(d.group_start, idx, &cand) {
                continue;
            }
            self.locals.push((d.var, Value::Rel(cand)));
            self.ltypes.push((d.var, d_ty.clone()));
            let res = self.some_rec(items, idx + 1, body, t, negated_body, any_of);
            self.locals.truncate(old_l);
            self.ltypes.truncate(old_lt);
            if res? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn all_rec(
        &mut self,
        items: &[DeclVar],
        idx: usize,
        body: &RExpr,
        t: usize,
        any_of: &mut bool,
    ) -> Result<bool, EvalError> {
        if idx == items.len() {
            let br = self.eval_bool_pol(body, t, false)?;
            if self.env.no_overflow && br.of {
                // Alloy/Kodkod noOverflow: overflowing valuation inside `all` does not falsify it.
                return Ok(true);
            }
            return Ok(br.val);
        }
        let d = items[idx].clone();
        let (domain, bof) = self.resolve_decl_bound(&d, t)?;
        *any_of |= bof;
        let cands = self.enumerate_domain(&domain, &d.bound_expr, d.mult, d.is_unary_one, t)?;
        let d_ty = self.rty(&d.inner_expr).unwrap_or_else(Self::empty_ty);
        let old_l = self.locals.len();
        let old_lt = self.ltypes.len();
        for cand in cands {
            if d.group_start < idx && !self.disj_ok(d.group_start, idx, &cand) {
                continue;
            }
            self.locals.push((d.var, Value::Rel(cand)));
            self.ltypes.push((d.var, d_ty.clone()));
            let ok = self.all_rec(items, idx + 1, body, t, any_of)?;
            self.locals.truncate(old_l);
            self.ltypes.truncate(old_lt);
            if !ok {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn count_rec(
        &mut self,
        items: &[DeclVar],
        idx: usize,
        body: &RExpr,
        t: usize,
        count: &mut usize,
        limit: usize,
        any_of: &mut bool,
    ) -> Result<(), EvalError> {
        if *count >= limit {
            return Ok(());
        }
        if idx == items.len() {
            let br = self.eval_bool_pol(body, t, false)?;
            *any_of |= br.of;
            if br.val && (!self.env.no_overflow || !br.of) {
                *count += 1;
            }
            return Ok(());
        }
        let d = items[idx].clone();
        let (domain, bof) = self.resolve_decl_bound(&d, t)?;
        *any_of |= bof;
        let cands = self.enumerate_domain(&domain, &d.bound_expr, d.mult, d.is_unary_one, t)?;
        let d_ty = self.rty(&d.inner_expr).unwrap_or_else(Self::empty_ty);
        let old_l = self.locals.len();
        let old_lt = self.ltypes.len();
        for cand in cands {
            if *count >= limit {
                break;
            }
            if d.group_start < idx && !self.disj_ok(d.group_start, idx, &cand) {
                continue;
            }
            self.locals.push((d.var, Value::Rel(cand)));
            self.ltypes.push((d.var, d_ty.clone()));
            self.count_rec(items, idx + 1, body, t, count, limit, any_of)?;
            self.locals.truncate(old_l);
            self.ltypes.truncate(old_lt);
        }
        Ok(())
    }

    fn enumerate_domain(
        &mut self,
        domain: &RelVal,
        bound_expr: &RExpr,
        mult: Option<UnOp>,
        is_unary_one: bool,
        t: usize,
    ) -> Result<Vec<RelVal>, EvalError> {
        if is_unary_one {
            return Ok(domain
                .tuples
                .iter()
                .map(|row| RelVal::singleton(1, row.clone()))
                .collect());
        }
        if domain.arity == 1 && mult == Some(UnOp::Lone) {
            let mut out = Vec::with_capacity(domain.len() + 1);
            out.push(RelVal::empty(1));
            for row in &domain.tuples {
                out.push(RelVal::singleton(1, row.clone()));
            }
            return Ok(out);
        }
        // Special fast enumeration for functional arrow bounds `A -> one B` or `A -> lone B` or `seq B`
        let (_, inner_no_mult) = decl_mult(bound_expr);
        if let RExpr::Bin(BinOp::Arrow(Mult::Set, rm @ (Mult::One | Mult::Lone)), a_expr, b_expr) =
            inner_no_mult
        {
            if let (Ok((a, _)), Ok((b, _))) = (self.eval_rel(a_expr, t), self.eval_rel(b_expr, t)) {
                if a.arity == 1 && b.arity == 1 && !is_mult_arrow(a_expr) && !is_mult_arrow(b_expr) {
                    let per_a = b.len() + usize::from(*rm == Mult::Lone);
                    if let Some(total) = per_a.checked_pow(a.len() as u32) {
                        if total <= 1_000_000 {
                            let mut funcs = Vec::with_capacity(total);
                            let mut cur = Vec::new();
                            enum_func(&a.tuples, &b.tuples, *rm == Mult::Lone, 0, &mut cur, &mut funcs);
                            return Ok(funcs);
                        }
                    }
                }
            }
        }
        // General higher-order powerset up to cap 20 elements
        if domain.len() > 20 {
            return Err(EvalError::new(format!(
                "higher-order domain too large ({} tuples) without valid skolem witness",
                domain.len()
            )));
        }
        let n = domain.len();
        let total = 1usize << n;
        let mut out = Vec::new();
        for mask in 0..total {
            if mult == Some(UnOp::Some) && mask == 0 {
                continue;
            }
            let mut tuples = Vec::new();
            for (bit, row) in domain.tuples.iter().enumerate() {
                if (mask >> bit) & 1 != 0 {
                    tuples.push(row.clone());
                }
            }
            let cand = RelVal { arity: domain.arity, tuples };
            if is_mult_arrow(bound_expr) {
                let (ok, _) = self.eval_is_in(&cand, bound_expr, t)?;
                if !ok {
                    continue;
                }
            }
            out.push(cand);
        }
        Ok(out)
    }
}

#[derive(Clone)]
struct DeclVar {
    var: LocalId,
    #[allow(dead_code)]
    disjoint: bool,
    group_start: usize,
    bound_expr: RExpr,
    inner_expr: RExpr,
    mult: Option<UnOp>,
    arity: u32,
    is_unary_one: bool,
}

struct FlatDecls {
    items: Vec<DeclVar>,
    of: bool,
}

fn enum_func(
    dom: &[Vec<AtomIdx>],
    rng: &[Vec<AtomIdx>],
    allow_empty: bool,
    idx: usize,
    cur: &mut Vec<Vec<AtomIdx>>,
    out: &mut Vec<RelVal>,
) {
    if idx == dom.len() {
        out.push(RelVal::from_tuples(2, cur.clone()));
        return;
    }
    let a = dom[idx][0];
    if allow_empty {
        enum_func(dom, rng, allow_empty, idx + 1, cur, out);
    }
    for b in rng {
        cur.push(vec![a, b[0]]);
        enum_func(dom, rng, allow_empty, idx + 1, cur, out);
        cur.pop();
    }
}

pub(crate) fn decl_mult(e: &RExpr) -> (Option<UnOp>, &RExpr) {
    match e {
        RExpr::Un(op @ (UnOp::Set | UnOp::One | UnOp::Lone | UnOp::Some | UnOp::ExactlyOf), x) => {
            (Some(*op), x)
        }
        _ => (None, e),
    }
}

fn is_mult_arrow(e: &RExpr) -> bool {
    match e {
        RExpr::Bin(BinOp::Arrow(l, r), a, b) => {
            !(*l == Mult::Set && *r == Mult::Set) || is_mult_arrow(a) || is_mult_arrow(b)
        }
        RExpr::Un(UnOp::Seq, _) => true,
        _ => false,
    }
}

fn mult_ok(m: Mult, count: usize) -> bool {
    match m {
        Mult::Set => true,
        Mult::One => count == 1,
        Mult::Lone => count <= 1,
        Mult::Some => count >= 1,
    }
}

fn check_total_order(elem: &RelVal, first: &RelVal, next: &RelVal) -> bool {
    if elem.is_empty() || first.len() != 1 || next.len() + 1 != elem.len() {
        return false;
    }
    let f = first.tuples[0][0];
    if !elem.contains(&[f]) {
        return false;
    }
    let mut succ: HashMap<AtomIdx, AtomIdx> = HashMap::with_capacity(next.len());
    for pair in &next.tuples {
        if !elem.contains(&[pair[0]]) || !elem.contains(&[pair[1]]) {
            return false;
        }
        if succ.insert(pair[0], pair[1]).is_some() {
            return false;
        }
    }
    let mut visited = BTreeSet::new();
    let mut cur = f;
    while visited.insert(cur) {
        match succ.get(&cur) {
            Some(&nx) => cur = nx,
            None => break,
        }
    }
    visited.len() == elem.len()
}

fn sum_slice(vals: &[i32], bitwidth: i32) -> (i32, bool) {
    if vals.is_empty() {
        return (0, false);
    }
    if vals.len() == 1 {
        return wrap_int(vals[0] as i64, bitwidth);
    }
    let mid = vals.len() / 2;
    let (l, ol) = sum_slice(&vals[..mid], bitwidth);
    let (r, or) = sum_slice(&vals[mid..], bitwidth);
    let (s, os) = wrap_int(l as i64 + r as i64, bitwidth);
    (s, ol || or || os)
}

fn int_div(a: i32, b: i32, min: i32) -> (i32, bool) {
    if a == 0 {
        (0, b == 0)
    } else if b == 0 {
        (if a < 0 { 1 } else { -1 }, true)
    } else if a == min && b == -1 {
        (min, true)
    } else {
        (a / b, false)
    }
}

fn int_rem(a: i32, b: i32, min: i32) -> (i32, bool) {
    if b == 0 {
        (a, true)
    } else if a == min && b == -1 {
        (0, false)
    } else {
        (a % b, false)
    }
}

fn bit_at(v: i32, i: usize, width: usize) -> bool {
    let idx = i.min(width - 1);
    ((v >> idx) & 1) != 0
}

/// Bit-exact match to Kodkod's two's-complement left shift (`int_shl`).
fn int_shl(a: i32, b: i32, bitwidth: i32) -> (i32, bool) {
    if bitwidth <= 0 {
        return (0, false);
    }
    let width = bitwidth as usize;
    let mut bits: Vec<bool> = (0..width).map(|i| ((a >> i) & 1) != 0).collect();
    let max = 32 - ((width as u32 - 1).leading_zeros() as usize);
    let mut overflow = false;
    for i in 0..width {
        let shift = 1usize << i;
        let bbit = bit_at(b, i, width);
        if bbit {
            for x in 0..shift {
                let b1 = if width as isize - x as isize - 1 < 0 {
                    false
                } else {
                    bits[width - x - 1]
                };
                let b2 = if width as isize - x as isize - 2 < 0 {
                    false
                } else {
                    bits[width - x - 2]
                };
                if b1 != b2 {
                    overflow = true;
                    break;
                }
            }
        }
        if i < max && bbit {
            for j in (0..width).rev() {
                bits[j] = if j < shift { false } else { bits[j - shift] };
            }
        }
    }
    let mut val = 0i64;
    for j in 0..width - 1 {
        if bits[j] {
            val += 1i64 << j;
        }
    }
    if bits[width - 1] {
        val -= 1i64 << (width - 1);
    }
    (val as i32, overflow)
}

/// Bit-exact match to Kodkod's two's-complement right shift (`int_shr` / `int_sha`).
fn int_shr(a: i32, b: i32, bitwidth: i32, arithmetic: bool) -> (i32, bool) {
    if bitwidth <= 0 {
        return (0, false);
    }
    let width = bitwidth as usize;
    let mut bits: Vec<bool> = (0..width).map(|i| ((a >> i) & 1) != 0).collect();
    let sign = if arithmetic { bits[width - 1] } else { false };
    let max = 32 - ((width as u32 - 1).leading_zeros() as usize);
    for i in 0..max {
        let shift = 1usize << i;
        if bit_at(b, i, width) {
            let fill = width.saturating_sub(shift);
            for j in 0..width {
                bits[j] = if j < fill { bits[j + shift] } else { sign };
            }
        }
    }
    let mut val = 0i64;
    for j in 0..width - 1 {
        if bits[j] {
            val += 1i64 << j;
        }
    }
    if bits[width - 1] {
        val -= 1i64 << (width - 1);
    }
    (val as i32, false)
}

fn java_small_int(e: &RExpr, small: &mut Vec<LocalId>) -> bool {
    match e {
        RExpr::Num(_) | RExpr::Un(UnOp::Card | UnOp::Neg, _) | RExpr::Quant(Quant::Sum, ..) => true,
        RExpr::Un(UnOp::SigInt, x) => java_small_int(x, small),
        RExpr::Bin(
            BinOp::IntPlus
            | BinOp::IntMinus
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Rem
            | BinOp::Shl
            | BinOp::Shr
            | BinOp::Sha,
            ..,
        ) => true,
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
