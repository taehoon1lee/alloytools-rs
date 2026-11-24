//! Alloy 6 lasso time model (`past_depth`, multi-unroll horizon, `expr_is_temporal`).

use alloy_core::sema::{FuncId, Model, RExpr};
use alloy_core::syntax::{BinOp, UnOp};

/// Returns true iff `expr` (or any transitively called function body) mentions a `var` sig/field or temporal op.
pub fn expr_is_temporal(model: &Model, expr: &RExpr) -> bool {
    let mut visited = Vec::new();
    is_temporal_rec(model, expr, &mut visited)
}

fn is_temporal_rec(model: &Model, expr: &RExpr, visited: &mut Vec<FuncId>) -> bool {
    match expr {
        RExpr::Sig(s) => model.sigs.get(*s as usize).is_some_and(|sig| sig.is_var),
        RExpr::Field(f) => model.fields.get(*f as usize).is_some_and(|fld| fld.is_var),
        RExpr::Local(_) | RExpr::Const(_) | RExpr::Num(_) | RExpr::Str(_) => false,
        RExpr::Un(op, x) => {
            matches!(
                op,
                UnOp::Prime
                    | UnOp::Always
                    | UnOp::Eventually
                    | UnOp::Historically
                    | UnOp::Once
                    | UnOp::Before
                    | UnOp::After
            ) || is_temporal_rec(model, x, visited)
        }
        RExpr::Bin(op, a, b) => {
            matches!(op, BinOp::Until | BinOp::Releases | BinOp::Since | BinOp::Triggered)
                || is_temporal_rec(model, a, visited)
                || is_temporal_rec(model, b, visited)
        }
        RExpr::Quant(_, ds, b) | RExpr::Compr(ds, b) => {
            ds.iter().any(|d| is_temporal_rec(model, &d.bound, visited))
                || is_temporal_rec(model, b, visited)
        }
        RExpr::Ite(c, a, b) => {
            is_temporal_rec(model, c, visited)
                || is_temporal_rec(model, a, visited)
                || is_temporal_rec(model, b, visited)
        }
        RExpr::Let(bs, b) => {
            bs.iter().any(|(_, e)| is_temporal_rec(model, e, visited))
                || is_temporal_rec(model, b, visited)
        }
        RExpr::Call(fid, args) => {
            if args.iter().any(|a| is_temporal_rec(model, a, visited)) {
                return true;
            }
            if visited.contains(fid) {
                return false;
            }
            visited.push(*fid);
            let res = model
                .funcs
                .get(*fid as usize)
                .is_some_and(|f| is_temporal_rec(model, &f.body, visited));
            visited.pop();
            res
        }
        RExpr::Block(xs) | RExpr::Disj(xs) | RExpr::TotalOrder(xs) | RExpr::Choice(xs) => {
            xs.iter().any(|x| is_temporal_rec(model, x, visited))
        }
    }
}

/// Nesting depth of past temporal operators (`Before`, `Once`, `Historically`, `Since`, `Triggered`),
/// mirroring Java Alloy's `TemporalTranslator.countHeight - 1`.
pub fn past_depth(model: &Model, expr: &RExpr) -> usize {
    let mut visited = Vec::new();
    past_depth_rec(model, expr, &mut visited)
}

fn past_depth_rec(model: &Model, expr: &RExpr, visited: &mut Vec<FuncId>) -> usize {
    match expr {
        RExpr::Sig(_)
        | RExpr::Field(_)
        | RExpr::Local(_)
        | RExpr::Const(_)
        | RExpr::Num(_)
        | RExpr::Str(_) => 0,
        RExpr::Un(op, x) => {
            let add = usize::from(matches!(op, UnOp::Before | UnOp::Once | UnOp::Historically));
            add + past_depth_rec(model, x, visited)
        }
        RExpr::Bin(op, a, b) => {
            let add = usize::from(matches!(op, BinOp::Since | BinOp::Triggered));
            add + past_depth_rec(model, a, visited).max(past_depth_rec(model, b, visited))
        }
        RExpr::Quant(_, ds, b) | RExpr::Compr(ds, b) => ds
            .iter()
            .map(|d| past_depth_rec(model, &d.bound, visited))
            .max()
            .unwrap_or(0)
            .max(past_depth_rec(model, b, visited)),
        RExpr::Ite(c, a, b) => past_depth_rec(model, c, visited)
            .max(past_depth_rec(model, a, visited))
            .max(past_depth_rec(model, b, visited)),
        RExpr::Let(bs, b) => bs
            .iter()
            .map(|(_, e)| past_depth_rec(model, e, visited))
            .max()
            .unwrap_or(0)
            .max(past_depth_rec(model, b, visited)),
        RExpr::Call(fid, args) => {
            let args_d = args
                .iter()
                .map(|a| past_depth_rec(model, a, visited))
                .max()
                .unwrap_or(0);
            if visited.contains(fid) {
                return args_d;
            }
            visited.push(*fid);
            let body_d = model
                .funcs
                .get(*fid as usize)
                .map_or(0, |f| past_depth_rec(model, &f.body, visited));
            visited.pop();
            args_d.max(body_d)
        }
        RExpr::Block(xs) | RExpr::Disj(xs) | RExpr::TotalOrder(xs) | RExpr::Choice(xs) => xs
            .iter()
            .map(|x| past_depth_rec(model, x, visited))
            .max()
            .unwrap_or(0),
    }
}

/// Finite unrolled time horizon representing the infinite lasso `s_0..s_{l-1} (s_l..s_{k-1})^omega`
/// up to past-operator distinguishing depth `h` (`n_max = k + h * (k - l)`).
#[derive(Debug, Clone, Copy)]
pub struct TimeHorizon {
    pub k: usize,
    pub l: usize,
    pub p: usize,
    pub n_max: usize,
    pub is_temporal: bool,
}

impl TimeHorizon {
    pub fn new(n_states: usize, loop_state: Option<usize>, h: usize) -> Self {
        match loop_state {
            None => TimeHorizon {
                k: n_states.max(1),
                l: 0,
                p: 1,
                n_max: 1,
                is_temporal: false,
            },
            Some(l) => {
                let k = n_states.max(1);
                let l = l.min(k - 1);
                let p = k - l;
                let n_max = k + h * p;
                TimeHorizon { k, l, p, n_max, is_temporal: true }
            }
        }
    }

    #[inline]
    pub fn state_of(&self, t: usize) -> usize {
        if !self.is_temporal {
            0
        } else if t < self.k {
            t
        } else {
            self.l + ((t - self.l) % self.p)
        }
    }

    #[inline]
    pub fn step_next(&self, t: usize) -> usize {
        if !self.is_temporal {
            0
        } else if t + 1 < self.n_max {
            t + 1
        } else {
            self.n_max - self.p
        }
    }

    /// Finite prefix-plus-one-loop trace of future time indices starting at `t`.
    pub fn future_seq(&self, t: usize) -> Vec<usize> {
        if !self.is_temporal {
            return vec![0];
        }
        let mut seq = Vec::with_capacity(self.n_max);
        let mut seen = vec![false; self.n_max];
        let mut cur = t.min(self.n_max - 1);
        while !seen[cur] {
            seen[cur] = true;
            seq.push(cur);
            cur = self.step_next(cur);
        }
        seq
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lasso_horizon_maps_states_and_steps_accurately() {
        // Lasso: s0 -> s1 -> s2 -> loop to s1 (k=3, l=1, p=2)
        // With h=0: indices 0, 1, 2; step_next(2) == 1.
        let h0 = TimeHorizon::new(3, Some(1), 0);
        assert_eq!(h0.n_max, 3);
        assert_eq!(h0.step_next(0), 1);
        assert_eq!(h0.step_next(1), 2);
        assert_eq!(h0.step_next(2), 1);
        assert_eq!(h0.future_seq(0), vec![0, 1, 2]);
        assert_eq!(h0.future_seq(2), vec![2, 1]);

        // With h=1: indices 0, 1(u0), 2(u0), 3(u1=s1), 4(u1=s2); step_next(4) == 3.
        let h1 = TimeHorizon::new(3, Some(1), 1);
        assert_eq!(h1.n_max, 5);
        assert_eq!((0..5).map(|t| h1.state_of(t)).collect::<Vec<_>>(), vec![0, 1, 2, 1, 2]);
        assert_eq!(h1.step_next(2), 3);
        assert_eq!(h1.step_next(4), 3);
        assert_eq!(h1.future_seq(2), vec![2, 3, 4]);

        // With h=2: indices 0..7; state_of distinguishes first vs second vs third loop visit.
        let h2 = TimeHorizon::new(3, Some(1), 2);
        assert_eq!(h2.n_max, 7);
        assert_eq!(h2.state_of(5), 1);
        assert_eq!(h2.state_of(6), 2);
        assert_eq!(h2.step_next(6), 5);
    }
}
