//! Overload (`ExprChoice`) resolution for the exact pipeline: the shared `crate::resolve::Resolver` with the
//! locals' atom-level types tracked while translating.

use super::*;
use crate::resolve::Resolver;
use crate::translate::type_of;
use kodkod::instance::TupleSet as KTs;

impl<'a> Resolver for Cx<'a> {
    fn model(&self) -> &Model {
        self.model
    }
    fn rty(&mut self, e: &RExpr) -> Option<KTs> {
        self.ty(e)
    }
}

impl<'a> Cx<'a> {
    /// atom-level type (fast-translator universe) of an Alloy expression in the current scope
    pub(super) fn ty(&mut self, e: &RExpr) -> Option<KTs> {
        let n_atoms = self.lay.atoms.len() as u32
            + if self.max >= self.min {
                (self.max - self.min + 1) as u32
            } else {
                0
            };
        let mut memo = std::mem::take(&mut self.ty_memo);
        let mut env: HashMap<LocalId, KTs> = self.ltypes.iter().cloned().collect();
        let r = type_of(
            self.model,
            &self.lay,
            n_atoms,
            e,
            &mut memo,
            &mut Vec::new(),
            &mut env,
        )
        .ok();
        self.ty_memo = memo;
        r
    }

    pub(super) fn bind_type(&mut self, l: LocalId, e: &RExpr) {
        let t = self
            .ty(e)
            .unwrap_or_else(|| KTs::from_tuples(1, std::iter::empty::<Vec<u32>>()));
        self.ltypes.push((l, t));
    }
}
