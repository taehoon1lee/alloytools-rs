//! Port of `kodkod.engine.fol2sat.{SymmetryDetector, SymmetryBreaker}`.
//! `SymmetryDetector` iterates a `java.util.HashMap<IntSet,IntSet>`, so its bucket order is emulated exactly
//! (`IntSet.hashCode` = superFastHash over the elements, `HashMap.hash`, resize splitting, treeify-resize).

use crate::ast::*;
use crate::bool::*;
use crate::fol2bool::Leaf;
use crate::instance::{Bounds, Options, TupleSet};

fn intset_hash(s: &[u32]) -> i32 {
    let mut h = s.len() as i32;
    for &x in s {
        h = crate::bool::sfh_incremental(x as i32, h);
    }
    crate::bool::sfh_avalanche(h)
}

/// `java.util.HashMap<IntSet, IntSet>` insertion/iteration behaviour.
struct JHashMap {
    table: Vec<Vec<usize>>,
    threshold: i32,
    entries: Vec<(Vec<u32>, i32, Vec<u32>)>,
    size: usize,
}

impl JHashMap {
    fn new(initial: i32) -> JHashMap {
        JHashMap { table: Vec::new(), threshold: table_size_for(initial), entries: Vec::new(), size: 0 }
    }
    fn hash(key: &[u32]) -> i32 {
        let h = intset_hash(key);
        h ^ ((h as u32) >> 16) as i32
    }
    fn resize(&mut self) {
        let old_cap = self.table.len() as i32;
        let old_thr = self.threshold;
        let (new_cap, mut new_thr);
        if old_cap > 0 {
            new_cap = old_cap << 1;
            new_thr = if old_cap >= 16 { old_thr << 1 } else { 0 };
        } else if old_thr > 0 {
            new_cap = old_thr;
            new_thr = 0;
        } else {
            new_cap = 16;
            new_thr = 12;
        }
        if new_thr == 0 {
            new_thr = (new_cap as f32 * 0.75f32) as i32;
        }
        self.threshold = new_thr;
        let mut nt: Vec<Vec<usize>> = vec![Vec::new(); new_cap as usize];
        for (j, bin) in self.table.iter().enumerate() {
            if bin.is_empty() {
                continue;
            }
            let (mut lo, mut hi) = (Vec::new(), Vec::new());
            for &e in bin {
                if (self.entries[e].1 & old_cap) == 0 {
                    lo.push(e);
                } else {
                    hi.push(e);
                }
            }
            if bin.len() == 1 {
                let e = bin[0];
                nt[(self.entries[e].1 & (new_cap - 1)) as usize].push(e);
            } else {
                nt[j] = lo;
                nt[j + old_cap as usize] = hi;
            }
        }
        self.table = nt;
    }
    fn get_mut(&mut self, key: &[u32]) -> Option<&mut Vec<u32>> {
        if self.table.is_empty() {
            return None;
        }
        let h = Self::hash(key);
        let i = (h & (self.table.len() as i32 - 1)) as usize;
        let idx = self.table[i].iter().copied().find(|&e| self.entries[e].1 == h && self.entries[e].0 == key)?;
        Some(&mut self.entries[idx].2)
    }
    fn put(&mut self, key: Vec<u32>, val: Vec<u32>) {
        if self.table.is_empty() {
            self.resize();
        }
        let h = Self::hash(&key);
        let n = self.table.len() as i32;
        let i = (h & (n - 1)) as usize;
        if let Some(&e) = self.table[i].iter().find(|&&e| self.entries[e].1 == h && self.entries[e].0 == key) {
            self.entries[e].2 = val;
            return;
        }
        let bin_count_before = self.table[i].len();
        let e = self.entries.len();
        self.entries.push((key, h, val));
        self.table[i].push(e);
        if bin_count_before >= 8 {
            // treeifyBin: tables below MIN_TREEIFY_CAPACITY are resized instead
            if self.table.len() < 64 {
                self.resize();
            }
        }
        self.size += 1;
        if self.size as i32 > self.threshold {
            self.resize();
        }
    }
    fn clear(&mut self) {
        if self.size > 0 {
            self.size = 0;
            for b in &mut self.table {
                b.clear();
            }
        }
    }
    fn iter(&self) -> Vec<(Vec<u32>, Vec<u32>)> {
        let mut v = Vec::with_capacity(self.size);
        for bin in &self.table {
            for &e in bin {
                v.push((self.entries[e].0.clone(), self.entries[e].2.clone()));
            }
        }
        v
    }
}

fn table_size_for(cap: i32) -> i32 {
    let n = if cap <= 1 { 0 } else { (-1i32 as u32 >> (cap - 1).leading_zeros()) as i32 };
    if n < 0 {
        1
    } else if n >= (1 << 30) {
        1 << 30
    } else {
        n + 1
    }
}

fn set_insert(s: &mut Vec<u32>, x: u32) {
    if let Err(p) = s.binary_search(&x) {
        s.insert(p, x);
    }
}

/// `SymmetryDetector.partition(bounds)`
pub fn partition(b: &Bounds, ast: &Ast) -> Vec<Vec<u32>> {
    let usize_ = b.universe_size();
    let mut parts: Vec<Vec<u32>> = vec![(0..usize_).collect()];
    if usize_ == 1 {
        return parts;
    }
    let mut map = JHashMap::new(((usize_ * 2) / 3) as i32);
    for ts in b.ints.values() {
        refine(&mut parts, &ts.idx, 1, usize_, &mut map);
    }
    let mut sets: Vec<TupleSet> = Vec::new();
    for r in b.relations() {
        if ast.rel_info(r).atom {
            continue;
        }
        let lo = &b.lower[&r];
        let hi = &b.upper[&r];
        if !lo.is_empty() && lo.len() < hi.len() {
            sets.push(lo.clone());
        }
        if !hi.is_empty() {
            sets.push(hi.clone());
        }
    }
    sets.sort_by_key(|s| s.len());
    for s in sets {
        if parts.len() == usize_ as usize {
            break;
        }
        refine(&mut parts, &s.idx, s.arity, usize_, &mut map);
    }
    parts
}

fn refine1(parts: &mut Vec<Vec<u32>>, set: &[u32]) {
    let mut i = 0;
    while i < parts.len() {
        let inter: Vec<u32> = parts[i].iter().copied().filter(|x| set.binary_search(x).is_ok()).collect();
        if !inter.is_empty() && inter.len() < parts[i].len() {
            parts[i].retain(|x| inter.binary_search(x).is_err());
            parts.insert(i + 1, inter);
            i += 2;
        } else {
            i += 1;
        }
    }
}

fn refine(parts: &mut Vec<Vec<u32>>, set: &[u32], arity: u32, n: u32, map: &mut JHashMap) {
    if arity == 1 {
        refine1(parts, set);
        return;
    }
    let mut other_columns: Vec<Vec<u32>> = Vec::new();
    let fcf = n.pow(arity - 1);
    let mut first_col: Vec<u32> = Vec::new();
    for &t in set {
        set_insert(&mut first_col, t / fcf);
    }
    refine1(parts, &first_col);
    let iden_factor = ((1i64 - fcf as i64) / (1i64 - n as i64)) as u32;
    let mut i = 0;
    while i < parts.len() {
        if first_col.binary_search(&parts[i][0]).is_ok() {
            map.clear();
            let part = parts[i].clone();
            for &atom in &part {
                let lo = atom * fcf;
                let hi = (atom + 1) * fcf - 1;
                let start = set.partition_point(|&x| x < lo);
                let mut range: Vec<u32> = Vec::new();
                for &t in &set[start..] {
                    if t > hi {
                        break;
                    }
                    set_insert(&mut range, t % fcf);
                }
                match map.get_mut(&range) {
                    Some(dom) => set_insert(dom, atom),
                    None => map.put(range, vec![atom]),
                }
            }
            parts.remove(i);
            let mut pos = i;
            let mut iden: Vec<u32> = Vec::new();
            for (key, val) in map.iter() {
                if val.len() == 1 && key.len() == 1 && key[0] == val[0] * iden_factor {
                    set_insert(&mut iden, val[0]);
                } else {
                    parts.insert(pos, val);
                    pos += 1;
                    other_columns.push(key);
                }
            }
            if !iden.is_empty() {
                parts.insert(pos, iden);
                pos += 1;
            }
            i = pos;
        } else {
            i += 1;
        }
    }
    for oc in other_columns {
        refine(parts, &oc, arity - 1, n, map);
    }
}

/// `SymmetryBreaker` (non-decomposed: stage bounds == bounds).
pub struct Breaker {
    pub symmetries: Vec<Vec<u32>>,
    n: u32,
}

impl Breaker {
    pub fn new(b: &Bounds, ast: &Ast) -> Breaker {
        Breaker { symmetries: partition(b, ast), n: b.universe_size() }
    }

    fn remove_partition(&mut self, atom: u32) {
        if let Some(i) = self.symmetries.iter().position(|p| p.binary_search(&atom).is_ok()) {
            self.symmetries.remove(i);
        }
    }

    fn symmetric_column_partitions(&self, b: &Bounds, r: N, arity: u32) -> Option<Vec<usize>> {
        let upper = &b.upper[&r];
        if upper.is_empty() {
            return None;
        }
        let n = self.n;
        let mut cols = vec![usize::MAX; arity as usize];
        let mut min = upper.idx[0];
        for i in (0..arity as usize).rev() {
            let a = min % n;
            cols[i] = self.symmetries.iter().position(|p| p.binary_search(&a).is_ok())?;
            min /= n;
        }
        for &t in &upper.idx {
            let mut tuple = t;
            for i in (0..arity as usize).rev() {
                if self.symmetries[cols[i]].binary_search(&(tuple % n)).is_err() {
                    return None;
                }
                tuple /= n;
            }
        }
        Some(cols)
    }

    /// `breakMatrixSymmetries(preds, aggressive=true).keySet()`
    pub fn break_matrix_symmetries(&mut self, ast: &Ast, b: &mut Bounds, totals: &[N], acyclics: &[N]) -> Vec<N> {
        let mut broken = Vec::new();
        let name = |p: &N| -> String {
            let r = match ast.get(*p) {
                Node::PTotal(r, ..) | Node::PAcyclic(r) => *r,
                _ => unreachable!(),
            };
            ast.rel_info(r).name.clone()
        };
        let mut ts = totals.to_vec();
        ts.sort_by_key(|p| name(p));
        for p in ts {
            if self.break_total_order(ast, b, p) {
                broken.push(p);
            }
        }
        let mut acs = acyclics.to_vec();
        acs.sort_by_key(|p| name(p));
        for p in acs {
            if self.break_acyclic(ast, b, p) {
                broken.push(p);
            }
        }
        broken
    }

    fn break_total_order(&mut self, ast: &Ast, b: &mut Bounds, p: N) -> bool {
        let (relation, ordered, first, last) = match ast.get(p) {
            Node::PTotal(r, o, f, l) => (*r, *o, *f, *l),
            _ => unreachable!(),
        };
        let n = self.n;
        let domain = b.upper[&ordered].idx.clone();
        if domain.is_empty() {
            return false;
        }
        let (dmin, dmax) = (domain[0], *domain.last().unwrap());
        if self.symmetric_column_partitions(b, ordered, 1).is_some() && b.upper[&first].contains(dmin) && b.upper[&last].contains(dmax) {
            let mut ordering = Vec::new();
            let mut prev = dmin;
            for &next in &domain {
                if next < prev + 1 || next > n {
                    continue;
                }
                ordering.push(prev * n + next);
                prev = next;
            }
            let ordering = TupleSet::new(2, ordering);
            if ordering.contains_all(&b.lower[&relation]) && b.upper[&relation].contains_all(&ordering) {
                self.remove_partition(dmin);
                b.bound_exactly(first, TupleSet::new(1, vec![dmin]));
                b.bound_exactly(last, TupleSet::new(1, vec![dmax]));
                let up = b.upper[&ordered].clone();
                b.bound_exactly(ordered, up);
                b.bound_exactly(relation, ordering);
                return true;
            }
        }
        false
    }

    fn break_acyclic(&mut self, ast: &Ast, b: &mut Bounds, p: N) -> bool {
        let relation = match ast.get(p) {
            Node::PAcyclic(r) => *r,
            _ => unreachable!(),
        };
        let n = self.n;
        let cols = match self.symmetric_column_partitions(b, relation, 2) {
            Some(c) => c,
            None => return false,
        };
        let upper = b.upper[&relation].clone();
        let mut reduced: Vec<u32> = Vec::new();
        for &t in &upper.idx {
            let mirror = (t / n) + (t % n) * n;
            if t != mirror {
                if !upper.contains(mirror) {
                    return false;
                }
                if reduced.binary_search(&mirror).is_err() {
                    set_insert(&mut reduced, t);
                }
            }
        }
        let min = self.symmetries[cols[0]][0];
        self.remove_partition(min);
        b.bound_upper(relation, TupleSet::new(2, reduced));
        true
    }

    fn permutation(&self, mut arity: u32, mut tuple: u32, a0: u32, a1: u32) -> u32 {
        let n = self.n;
        let mut perm = 0u32;
        let mut u = 1u32;
        while arity > 0 {
            let a = tuple % n;
            perm += if a == a0 {
                a1 * u
            } else if a == a1 {
                a0 * u
            } else {
                a * u
            };
            arity -= 1;
            tuple /= n;
            u = u.wrapping_mul(n);
        }
        perm
    }

    /// `generateSBP(interpreter, options)`
    pub fn generate_sbp(&mut self, ast: &Ast, b: &Bounds, leaf: &Leaf, f: &mut Factory, opt: &Options) -> Result<BV, String> {
        let pred_len = opt.symmetry as usize;
        if self.symmetries.is_empty() || pred_len == 0 {
            return Ok(TRUE);
        }
        let n = self.n;
        // relParts
        let mut rel_parts: Vec<(N, Vec<u32>)> = Vec::new();
        for r in b.relations() {
            let upper = &b.upper[&r];
            if upper.len() == b.lower[&r].len() {
                continue;
            }
            let arity = ast.rel_info(r).arity;
            let mut reps: Vec<u32> = Vec::new();
            for &t in &upper.idx {
                let mut ti = t;
                for _ in 0..arity {
                    let a = ti % n;
                    if let Some(p) = self.symmetries.iter().find(|p| p.binary_search(&a).is_ok()) {
                        set_insert(&mut reps, p[0]);
                    }
                    ti /= n;
                }
            }
            rel_parts.push((r, reps));
        }
        rel_parts.sort_by(|a, b| {
            let (ia, ib) = (ast.rel_info(a.0), ast.rel_info(b.0));
            ia.arity.cmp(&ib.arity).then_with(|| java_string_cmp(&ia.name, &ib.name))
        });
        let mut sbp = Acc::new(Op::And);
        let mut original: Vec<BV> = Vec::new();
        let mut permuted: Vec<BV> = Vec::new();
        let syms = self.symmetries.clone();
        // [HASLab] temporal expansions: the static entries first, then the entries of each time step in turn
        let times: Option<Vec<u32>> = b.state.filter(|s| b.lower.contains_key(s)).map(|s| b.lower[&s].idx.clone());
        let mut passes: Vec<Option<u32>> = vec![None];
        if let Some(ts) = &times {
            passes.extend(ts.iter().map(|&t| Some(t)));
        }
        let has_atom = |idx: u32, arity: u32, a: u32| -> bool {
            let mut x = idx;
            for _ in 0..arity {
                if x % n == a {
                    return true;
                }
                x /= n;
            }
            false
        };
        for sym in &syms {
            let mut prev = sym[0];
            for &cur in &sym[1..] {
                for &time in &passes {
                    for (r, reps) in &rel_parts {
                        if original.len() >= pred_len {
                            break;
                        }
                        if reps.binary_search(&sym[0]).is_err() {
                            continue;
                        }
                        let info = ast.rel_info(*r);
                        if info.skolem && opt.temporal {
                            continue;
                        }
                        let m = leaf.interpret_rel(*r, info.arity)?;
                        for (&idx, &val) in &m.cells {
                            let pidx = self.permutation(info.arity, idx, prev, cur);
                            let pval = m.get(pidx);
                            if pidx == idx || original.iter().zip(permuted.iter()).any(|(o, p)| *o == pval && *p == val) {
                                continue;
                            }
                            let in_state = times.as_ref().map_or(false, |ts| ts.binary_search(&(idx % n)).is_ok());
                            let take = match time {
                                None => !in_state,
                                Some(t) => has_atom(idx, info.arity, t),
                            };
                            if take {
                                original.push(val);
                                permuted.push(pval);
                            }
                        }
                    }
                }
                let l = leq(f, &original, &permuted);
                sbp.add(l);
                original.clear();
                permuted.clear();
                prev = cur;
            }
        }
        self.symmetries.clear();
        Ok(f.accumulate(&sbp))
    }
}

/// `String.compareTo` (UTF-16 code unit order)
pub fn java_string_cmp(a: &str, b: &str) -> std::cmp::Ordering {
    a.encode_utf16().cmp(b.encode_utf16())
}

fn leq(f: &mut Factory, l0: &[BV], l1: &[BV]) -> BV {
    let mut cmp = Acc::new(Op::And);
    let mut prev_equals = TRUE;
    for i in 0..l0.len() {
        let inner = f.implies(l0[i], l1[i]);
        let x = f.implies(prev_equals, inner);
        cmp.add(x);
        let e = f.iff(l0[i], l1[i]);
        prev_equals = f.and(prev_equals, e);
    }
    f.accumulate(&cmp)
}
