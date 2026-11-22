//! Port of `kodkod.engine.bool`: `BooleanValue` gates, `Operator`, `CBCFactory` (compact boolean circuits with
//! hash-consing), `BooleanFactory`, `BooleanAccumulator`, `Int`/`TwosComplementInt`, `DefCond`, `Dimensions`,
//! `BooleanMatrix`.
//!
//! A boolean value is its Kodkod *label* (`BV = i32`): variables `1..=maxVariable`, gates above that (labels are
//! the CNF variables, so creation order matters), a negation is `-label`, and the constants are `±i32::MAX`.
//! Everything that influences which gate gets which label (assembler rules, `CacheSet` chain order, `superFastHash`,
//! accumulator order, overflow gates) mirrors the Java code exactly.

use std::collections::{BTreeMap, BTreeSet};

pub type BV = i32;
pub const TRUE: BV = i32::MAX;
pub const FALSE: BV = -i32::MAX;

/// `kodkod.engine.bool.Operator` (ordinals matter: they select the assembler).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Op {
    And = 0,
    Or = 1,
    Ite = 2,
    Not = 3,
    Var = 4,
    Const = 5,
}

#[inline]
fn identity(op: Op) -> BV {
    if op == Op::And {
        TRUE
    } else {
        FALSE
    }
}
#[inline]
pub fn short_circuit(op: Op) -> BV {
    if op == Op::And {
        FALSE
    } else {
        TRUE
    }
}
#[inline]
fn complement(op: Op) -> Op {
    if op == Op::And {
        Op::Or
    } else {
        Op::And
    }
}

// ---------------------------------------------------------------------------------------------- hashing

/// `kodkod.util.ints.Ints.superFastHash(int)`
pub fn super_fast_hash(key: i32) -> i32 {
    sfh_avalanche(sfh_incremental(key, 11))
}
pub(crate) fn sfh_incremental(key: i32, hash: i32) -> i32 {
    let mut hash = hash.wrapping_add(key & 0xffff);
    let high16 = (((key as u32) >> 16) & 0xffff) as i32;
    let tmp = (high16 << 11) ^ hash;
    hash = (hash << 16) ^ tmp;
    hash.wrapping_add(hash >> 11)
}
pub(crate) fn sfh_avalanche(mut hash: i32) -> i32 {
    hash ^= hash << 3;
    hash = hash.wrapping_add(hash >> 5);
    hash ^= hash << 4;
    hash = hash.wrapping_add(hash >> 17);
    hash ^= hash << 25;
    hash.wrapping_add(hash >> 6)
}

/// `kodkod.util.collections.CacheSet` restricted to what `CBCFactory` uses: insertion at the chain head,
/// power-of-two table, `resize` reversing chains, `get(hash)` filtering by exact hash code.
struct CacheSet {
    table: Vec<u32>,
    /// (gate label, hashCode, next entry + 1)
    entries: Vec<(BV, i32, u32)>,
    size: usize,
    threshold: usize,
}

impl CacheSet {
    fn new() -> CacheSet {
        CacheSet { table: vec![0; 16], entries: Vec::new(), size: 0, threshold: 12 }
    }
    #[inline]
    fn hash(mut h: i32) -> i32 {
        h = h.wrapping_add(!(h << 9));
        h ^= ((h as u32) >> 14) as i32;
        h = h.wrapping_add(h << 4);
        h ^= ((h as u32) >> 10) as i32;
        h
    }
    #[inline]
    fn index_for(h: i32, len: usize) -> usize {
        (h & (len as i32 - 1)) as usize
    }
    fn add(&mut self, val: BV, hc: i32) {
        let i = Self::index_for(Self::hash(hc), self.table.len());
        self.entries.push((val, hc, self.table[i]));
        self.table[i] = self.entries.len() as u32;
        let old = self.size;
        self.size += 1;
        if old >= self.threshold {
            let ncap = 2 * self.table.len();
            let mut nt = vec![0u32; ncap];
            for j in 0..self.table.len() {
                let mut e = self.table[j];
                while e != 0 {
                    let next = self.entries[e as usize - 1].2;
                    let ni = Self::index_for(Self::hash(self.entries[e as usize - 1].1), ncap);
                    self.entries[e as usize - 1].2 = nt[ni];
                    nt[ni] = e;
                    e = next;
                }
            }
            self.table = nt;
            self.threshold = (ncap as f32 * 0.75f32) as usize;
        }
    }
    /// Candidates of `get(hash)` in iteration order.
    fn get(&self, hash: i32, out: &mut Vec<BV>) {
        out.clear();
        let mut e = self.table[Self::index_for(Self::hash(hash), self.table.len())];
        while e != 0 {
            let (v, hc, next) = self.entries[e as usize - 1];
            if hc == hash {
                out.push(v);
            }
            e = next;
        }
    }
}

// ---------------------------------------------------------------------------------------------- circuits

struct Gate {
    op: Op,
    /// And/Or: ascending labels (binary or n-ary); Ite: [if, then, else]
    inputs: Vec<BV>,
    /// the `hashcode` field of MultiGate / ITEGate
    hash: i32,
    /// `superFastHash(label)`
    lh: i32,
}

/// `BooleanAccumulator`: inputs keyed by label (a `TreeSequence`, ascending iteration).
#[derive(Clone, Debug)]
pub struct Acc {
    pub op: Op,
    pub inputs: BTreeSet<i32>,
}

impl Acc {
    pub fn new(op: Op) -> Acc {
        Acc { op, inputs: BTreeSet::new() }
    }
    /// Java `add`: returns the short-circuit constant, or 0 for "this".
    pub fn add(&mut self, v: BV) -> BV {
        let sc = short_circuit(self.op);
        if self.is_short_circuited() {
            return sc;
        }
        if v == sc || self.inputs.contains(&v.wrapping_neg()) {
            self.inputs.clear();
            self.inputs.insert(sc);
            return sc;
        }
        if v != identity(self.op) {
            self.inputs.insert(v);
        }
        0
    }
    pub fn is_short_circuited(&self) -> bool {
        self.inputs.len() == 1 && *self.inputs.iter().next().unwrap() == short_circuit(self.op)
    }
    pub fn len(&self) -> usize {
        self.inputs.len()
    }
    pub fn is_empty(&self) -> bool {
        self.inputs.is_empty()
    }
}

/// `BooleanFactory` (two's complement) over a `CBCFactory`.
pub struct Factory {
    gates: Vec<Gate>,
    label: i32,
    max_var: i32,
    num_vars: i32,
    cmp_max: i32,
    caches: [CacheSet; 3],
    pub bitwidth: i32,
    pub no_overflow: bool,
    scrap0: Vec<BV>,
    scrap1: Vec<BV>,
    cand: Vec<Vec<BV>>,
}

impl Factory {
    /// `BooleanFactory.factory(numVars, options)`: `comparisonDepth` = `options.sharing()`.
    pub fn new(num_vars: i32, sharing: i32, bitwidth: i32, no_overflow: bool) -> Factory {
        let cmp_max = if num_vars == 0 { 1 } else { 1 << sharing };
        let mut gates = Vec::with_capacity(num_vars as usize + 1);
        gates.push(Gate { op: Op::Const, inputs: Vec::new(), hash: 0, lh: 0 });
        for i in 1..=num_vars {
            gates.push(Gate { op: Op::Var, inputs: Vec::new(), hash: 0, lh: super_fast_hash(i) });
        }
        Factory {
            gates,
            label: num_vars + 1,
            max_var: num_vars,
            num_vars,
            cmp_max,
            caches: [CacheSet::new(), CacheSet::new(), CacheSet::new()],
            bitwidth,
            no_overflow,
            scrap0: Vec::new(),
            scrap1: Vec::new(),
            cand: Vec::new(),
        }
    }

    pub fn max_variable(&self) -> i32 {
        self.max_var
    }
    pub fn max_formula(&self) -> i32 {
        self.label - 1
    }
    pub fn num_variables(&self) -> i32 {
        self.num_vars
    }

    /// `BooleanFactory.addVariables` / `CBCFactory.addVariables`
    pub fn add_variables(&mut self, n: i32) {
        if n <= 0 {
            return;
        }
        for i in 0..n {
            let l = self.label + i;
            self.gates.push(Gate { op: Op::Var, inputs: Vec::new(), hash: 0, lh: super_fast_hash(l) });
        }
        self.label += n;
        self.max_var = self.label - 1;
        self.num_vars += n;
    }

    // ---- gate structure
    #[inline]
    pub fn op(&self, v: BV) -> Op {
        if v == TRUE || v == FALSE {
            Op::Const
        } else if v < 0 {
            Op::Not
        } else {
            self.gates[v as usize].op
        }
    }
    #[inline]
    fn size(&self, v: BV) -> usize {
        if v < 0 {
            1
        } else {
            self.gates[v as usize].inputs.len()
        }
    }
    /// Inputs of a gate (`-v`'s single input is `v`).
    pub fn inputs(&self, v: BV) -> &[BV] {
        &self.gates[v as usize].inputs
    }
    /// `BooleanFormula.hash(op)`
    #[inline]
    fn hash_op(&self, v: BV, op: Op) -> i32 {
        if v < 0 {
            return super_fast_hash(v);
        }
        let g = &self.gates[v as usize];
        match g.op {
            Op::And | Op::Or if g.op == op => g.hash,
            _ => g.lh,
        }
    }

    /// `BooleanFormula.contains(op, f, k)`
    fn contains(&self, v: BV, op: Op, f: i32, k: i32) -> i32 {
        if v < 0 || self.gates[v as usize].op == Op::Var {
            return if f == v { 1 } else { -1 };
        }
        let g = &self.gates[v as usize];
        let label = v;
        match g.op {
            Op::Ite => {
                if f == label {
                    1
                } else if op != Op::Ite || k < 3 || f > label || f.wrapping_neg() > label {
                    -1
                } else if g.inputs[0] == f || g.inputs[1] == f || g.inputs[2] == f {
                    3
                } else {
                    -3
                }
            }
            _ if g.inputs.len() == 2 => {
                if f == label {
                    return 1;
                }
                if g.op != op || k < 2 || f > label || f.wrapping_neg() > label {
                    return -1;
                }
                let (lo, hi) = (g.inputs[0], g.inputs[1]);
                let l = self.contains(lo, op, f, k - 1);
                if l > 0 {
                    return l;
                }
                let h = self.contains(hi, op, f, k - l);
                if h > 0 {
                    h - l
                } else {
                    h + l
                }
            }
            _ => {
                if f == label {
                    return 1;
                }
                if g.op != op || f > label || f.wrapping_neg() > label {
                    return -1;
                }
                let inputs = &g.inputs;
                let (mut low, mut high, mut step) = (0i32, inputs.len() as i32 - 1, 1);
                while low <= high && step <= k {
                    let mid = ((low + high) as u32 >> 1) as i32;
                    let mid_val = inputs[mid as usize];
                    if mid_val < f {
                        low = mid + 1;
                    } else if mid_val > f {
                        high = mid - 1;
                    } else {
                        return step;
                    }
                    step += 1;
                }
                1 - step
            }
        }
    }

    /// `BooleanFormula.flatten(op, set, k)` (identity set; insertion-ordered vec)
    fn flatten(&self, v: BV, op: Op, set: &mut Vec<BV>, k: i32) {
        #[inline]
        fn add(set: &mut Vec<BV>, v: BV) {
            if !set.contains(&v) {
                set.push(v);
            }
        }
        if v < 0 || self.gates[v as usize].op == Op::Var {
            add(set, v);
            return;
        }
        let g = &self.gates[v as usize];
        match g.op {
            Op::Ite => {
                if op == Op::Ite && k > 2 {
                    add(set, g.inputs[0]);
                    add(set, g.inputs[1]);
                    add(set, g.inputs[2]);
                } else {
                    add(set, v);
                }
            }
            _ if g.inputs.len() == 2 => {
                if g.op == op && k > 1 {
                    let old = set.len();
                    self.flatten(g.inputs[0], op, set, k - 1);
                    let used = (set.len() - old) as i32;
                    self.flatten(g.inputs[1], op, set, k - used);
                } else {
                    add(set, v);
                }
            }
            _ => {
                let n = g.inputs.len() as i32;
                if g.op == op && k >= n {
                    let mut diff = k - n;
                    for &f in &g.inputs {
                        let old = set.len();
                        self.flatten(f, op, set, diff.max(1));
                        diff -= (set.len() - old) as i32;
                    }
                } else {
                    add(set, v);
                }
            }
        }
    }

    fn set_eq(a: &[BV], b: &[BV]) -> bool {
        a.len() == b.len() && a.iter().all(|x| b.contains(x))
    }

    fn new_gate(&mut self, op: Op, inputs: Vec<BV>, hash: i32) -> BV {
        let l = self.label;
        self.label += 1;
        self.gates.push(Gate { op, inputs, hash, lh: super_fast_hash(l) });
        let ci = op as usize;
        self.caches[ci].add(l, hash);
        l
    }

    fn take_cand(&mut self) -> Vec<BV> {
        self.cand.pop().unwrap_or_default()
    }
    fn give_cand(&mut self, v: Vec<BV>) {
        self.cand.push(v);
    }

    // ---- CBCFactory.assemble(i, t, e)
    pub fn ite(&mut self, i: BV, t: BV, e: BV) -> BV {
        if i == TRUE || t == e {
            t
        } else if i == FALSE {
            e
        } else if t == TRUE || i == t {
            self.assemble2(Op::Or, i, e)
        } else if t == FALSE || i == t.wrapping_neg() {
            self.assemble2(Op::And, -i, e)
        } else if e == TRUE || i == e.wrapping_neg() {
            self.assemble2(Op::Or, -i, t)
        } else if e == FALSE || i == e {
            self.assemble2(Op::And, i, t)
        } else {
            let hash = 3i32
                .wrapping_mul(self.hash_op(i, Op::Ite))
                .wrapping_add(5i32.wrapping_mul(self.hash_op(t, Op::Ite)))
                .wrapping_add(7i32.wrapping_mul(self.hash_op(e, Op::Ite)));
            let mut cand = self.take_cand();
            self.caches[Op::Ite as usize].get(hash, &mut cand);
            let found = cand.iter().copied().find(|&g| {
                let gi = &self.gates[g as usize].inputs;
                gi[0] == i && gi[1] == t && gi[2] == e
            });
            self.give_cand(cand);
            match found {
                Some(g) => g,
                None => self.new_gate(Op::Ite, vec![i, t, e], hash),
            }
        }
    }

    pub fn not(&self, v: BV) -> BV {
        v.wrapping_neg()
    }
    pub fn and(&mut self, a: BV, b: BV) -> BV {
        self.assemble2(Op::And, a, b)
    }
    pub fn or(&mut self, a: BV, b: BV) -> BV {
        self.assemble2(Op::Or, a, b)
    }
    pub fn xor(&mut self, a: BV, b: BV) -> BV {
        self.ite(a, -b, b)
    }
    pub fn implies(&mut self, a: BV, b: BV) -> BV {
        self.assemble2(Op::Or, -a, b)
    }
    pub fn iff(&mut self, a: BV, b: BV) -> BV {
        self.ite(a, b, -b)
    }
    pub fn sum3(&mut self, v0: BV, v1: BV, cin: BV) -> BV {
        let x = self.xor(v0, v1);
        self.xor(cin, x)
    }
    pub fn carry(&mut self, v0: BV, v1: BV, cin: BV) -> BV {
        let a = self.and(v0, v1);
        let x = self.xor(v0, v1);
        let b = self.and(cin, x);
        self.or(a, b)
    }

    // ---- CBCFactory.assemble(op, v0, v1)
    pub fn assemble2(&mut self, op: Op, v0: BV, v1: BV) -> BV {
        let (l, h) = if (self.op(v0) as i32) < (self.op(v1) as i32) { (v0, v1) } else { (v1, v0) };
        let hop = self.op(h);
        if hop == Op::Const {
            return if h == identity(op) { l } else { h };
        }
        let o0 = self.op(l) as i32;
        let o1 = hop as i32;
        let idx = (o0 << 2) + o1 - ((o0 * (o0 - 1)) >> 1);
        match idx {
            0 | 5 => self.jo_j(op, l, h),
            1 => self.ao_o(op, l, h),
            2 | 6 => self.jo_i(op, l, h),
            3 | 7 => self.jo_n(op, l, h),
            4 | 8 => self.jo_x(op, l, h),
            9 | 14 => {
                if l == h {
                    l
                } else {
                    self.cache2(op, l, h)
                }
            }
            10 => self.io_n(op, l, h),
            11 => self.cache2(op, l, h),
            12 => self.no_n(op, l, h),
            13 => self.no_v(op, l, h),
            _ => unreachable!("assembler index {idx}"),
        }
    }

    fn jo_x(&mut self, op: Op, f0: BV, f1: BV) -> BV {
        let fop = self.op(f0);
        let label = f1;
        let cm = self.cmp_max;
        if self.contains(f0, fop, label, cm) > 0 {
            if op == fop {
                f0
            } else {
                f1
            }
        } else if op == fop && self.contains(f0, op, label.wrapping_neg(), cm) > 0 {
            short_circuit(op)
        } else {
            self.cache2(op, f0, f1)
        }
    }

    fn ao_o(&mut self, op: Op, f0: BV, f1: BV) -> BV {
        let mut s0 = std::mem::take(&mut self.scrap0);
        let mut s1 = std::mem::take(&mut self.scrap1);
        s0.clear();
        s1.clear();
        let cm = self.cmp_max;
        self.flatten(f0, self.op(f0), &mut s0, cm);
        self.flatten(f1, self.op(f1), &mut s1, cm);
        let hit = s1.iter().any(|x| s0.contains(x));
        self.scrap0 = s0;
        self.scrap1 = s1;
        if hit {
            return if op == Op::And { f0 } else { f1 };
        }
        if f0 < f1 {
            self.jo_x(op, f1, f0)
        } else {
            self.jo_x(op, f0, f1)
        }
    }

    fn jo_j(&mut self, op: Op, f0: BV, f1: BV) -> BV {
        if f0 == f1 {
            return f0;
        }
        let fop = self.op(f0);
        let mut s0 = std::mem::take(&mut self.scrap0);
        let mut s1 = std::mem::take(&mut self.scrap1);
        s0.clear();
        s1.clear();
        let cm = self.cmp_max;
        self.flatten(f0, fop, &mut s0, cm);
        self.flatten(f1, fop, &mut s1, cm);
        let r = if s0.len() < s1.len() && s0.iter().all(|x| s1.contains(x)) {
            Some(if op == fop { f1 } else { f0 })
        } else if s0.len() >= s1.len() && s1.iter().all(|x| s0.contains(x)) {
            Some(if op == fop { f0 } else { f1 })
        } else {
            None
        };
        self.scrap0 = s0;
        self.scrap1 = s1;
        match r {
            Some(x) => x,
            None if f0 < f1 => self.jo_x(op, f1, f0),
            None => self.jo_x(op, f0, f1),
        }
    }

    fn jo_i(&mut self, op: Op, f0: BV, f1: BV) -> BV {
        if f0 < f1 {
            self.cache2(op, f1, f0)
        } else {
            self.jo_x(op, f0, f1)
        }
    }

    fn jo_n(&mut self, op: Op, f0: BV, f1: BV) -> BV {
        if f0 == f1.wrapping_neg() {
            short_circuit(op)
        } else if f0 < f1.wrapping_abs() {
            self.no_x(op, f1, f0)
        } else {
            self.jo_x(op, f0, f1)
        }
    }

    fn io_n(&mut self, op: Op, f0: BV, f1: BV) -> BV {
        if f0 == f1.wrapping_neg() {
            short_circuit(op)
        } else if f0 < f1.wrapping_abs() {
            self.no_x(op, f1, f0)
        } else {
            self.cache2(op, f0, f1)
        }
    }

    fn no_x(&mut self, op: Op, f0: BV, f1: BV) -> BV {
        let label = f1;
        let inner = f0.wrapping_neg();
        let cm = self.cmp_max;
        if self.contains(inner, complement(op), label, cm) > 0 {
            short_circuit(op)
        } else if self.contains(inner, complement(op), label.wrapping_neg(), cm) > 0 {
            f0
        } else {
            self.cache2(op, f0, f1)
        }
    }

    fn no_n(&mut self, op: Op, f0: BV, f1: BV) -> BV {
        if f0 == f1 {
            f0
        } else if f0 < f1 {
            self.no_x(op, f0, f1)
        } else {
            self.no_x(op, f1, f0)
        }
    }

    fn no_v(&mut self, op: Op, f0: BV, f1: BV) -> BV {
        if f0 == f1.wrapping_neg() {
            short_circuit(op)
        } else {
            self.no_x(op, f0, f1)
        }
    }

    // ---- CBCFactory.cache(op, f0, f1)
    fn cache2(&mut self, op: Op, f0: BV, f1: BV) -> BV {
        let (l, h) = if f0 < f1 { (f0, f1) } else { (f1, f0) };
        let hash = self.hash_op(l, op).wrapping_add(self.hash_op(h, op));
        let mut cand = self.take_cand();
        self.caches[op as usize].get(hash, &mut cand);
        let mut found = None;
        if self.op(l) == op || self.op(h) == op {
            let mut s0 = std::mem::take(&mut self.scrap0);
            let mut s1 = std::mem::take(&mut self.scrap1);
            s0.clear();
            let cm = self.cmp_max;
            self.flatten(l, op, &mut s0, cm - 1);
            let k2 = cm - s0.len() as i32;
            self.flatten(h, op, &mut s0, k2);
            for &g in &cand {
                let gi = &self.gates[g as usize].inputs;
                if gi.len() == 2 && gi[0] == l && gi[1] == h {
                    found = Some(g);
                    break;
                }
                s1.clear();
                self.flatten(g, op, &mut s1, cm);
                if Self::set_eq(&s0, &s1) {
                    found = Some(g);
                    break;
                }
            }
            self.scrap0 = s0;
            self.scrap1 = s1;
        } else {
            for &g in &cand {
                let gi = &self.gates[g as usize].inputs;
                if gi.len() == 2 && gi[0] == l && gi[1] == h {
                    found = Some(g);
                    break;
                }
            }
        }
        self.give_cand(cand);
        match found {
            Some(g) => g,
            None => self.new_gate(op, vec![l, h], hash),
        }
    }

    // ---- CBCFactory.assemble(BooleanAccumulator)
    pub fn accumulate(&mut self, acc: &Acc) -> BV {
        let op = acc.op;
        let asize = acc.inputs.len();
        match asize {
            0 => identity(op),
            1 => *acc.inputs.iter().next().unwrap(),
            2 => {
                let mut it = acc.inputs.iter();
                let a = *it.next().unwrap();
                let b = *it.next().unwrap();
                self.assemble2(op, a, b)
            }
            _ => {
                let mut hash = 0i32;
                for &x in &acc.inputs {
                    hash = hash.wrapping_add(self.hash_op(x, op));
                }
                let mut cand = self.take_cand();
                self.caches[op as usize].get(hash, &mut cand);
                let mut found = None;
                let same = |gi: &[BV]| gi.len() == asize && gi.iter().zip(acc.inputs.iter()).all(|(a, b)| a == b);
                if asize as i32 > self.cmp_max {
                    for &g in &cand {
                        if same(&self.gates[g as usize].inputs) {
                            found = Some(g);
                            break;
                        }
                    }
                } else {
                    let mut s0 = std::mem::take(&mut self.scrap0);
                    let cm = self.cmp_max;
                    'lookup: for &g in &cand {
                        let gi = &self.gates[g as usize].inputs;
                        if same(gi) {
                            found = Some(g);
                            break;
                        } else if gi.len() < asize {
                            s0.clear();
                            self.flatten(g, op, &mut s0, cm);
                            if s0.len() == asize {
                                for v in &acc.inputs {
                                    if !s0.contains(v) {
                                        continue 'lookup;
                                    }
                                }
                                found = Some(g);
                                break;
                            }
                        }
                    }
                    self.scrap0 = s0;
                }
                self.give_cand(cand);
                match found {
                    Some(g) => g,
                    None => self.new_gate(op, acc.inputs.iter().copied().collect(), hash),
                }
            }
        }
    }

    /// Convenience: `accumulate(BooleanAccumulator.treeGate(op, values...))`.
    pub fn tree_gate(&mut self, op: Op, values: &[BV]) -> BV {
        let mut acc = Acc::new(op);
        for &v in values {
            if acc.add(v) != 0 {
                break;
            }
        }
        self.accumulate(&acc)
    }

    // ---------------------------------------------------------------------------- integers (TwosComplementInt)

    /// `BooleanFactory.integer(number)`
    pub fn integer(&self, number: i32) -> Int {
        self.integer_bit(number, TRUE)
    }

    /// `BooleanFactory.integer(number, bit)` (`TwosComplementInt(factory, number, bit)`)
    pub fn integer_bit(&self, number: i32, bit: BV) -> Int {
        let width = self.int_width_of(number);
        let mut bits = Vec::with_capacity(width as usize);
        for i in 0..width {
            bits.push(if number & (1i32.wrapping_shl(i as u32)) == 0 { FALSE } else { bit });
        }
        Int { bits, of: FALSE, acc_of: FALSE }
    }

    fn int_width_of(&self, number: i32) -> i32 {
        if number > 0 {
            (33 - (number as u32).leading_zeros() as i32).min(self.bitwidth)
        } else if number < 0 {
            (33 - ((!number) as u32).leading_zeros() as i32).min(self.bitwidth)
        } else {
            1
        }
    }

    /// `DefCond.merge(factory, of, a, b)` = or(or(of, a.accum), b.accum)
    fn merge_of(&mut self, of: BV, a: BV, b: BV) -> BV {
        let x = self.or(of, a);
        self.or(x, b)
    }

    fn eq_without_overflow(&mut self, a: &Int, b: &Int) -> BV {
        let mut cmp = Acc::new(Op::And);
        let w = a.width().max(b.width());
        for i in 0..w {
            let x = self.iff(a.bit(i), b.bit(i));
            if cmp.add(x) == FALSE {
                return FALSE;
            }
        }
        self.accumulate(&cmp)
    }
    pub fn int_eq(&mut self, a: &Int, b: &Int) -> BV {
        self.eq_without_overflow(a, b)
    }
    pub fn int_neq(&mut self, a: &Int, b: &Int) -> BV {
        -self.eq_without_overflow(a, b)
    }
    pub fn int_lte(&mut self, a: &Int, b: &Int) -> BV {
        let mut cmp = Acc::new(Op::And);
        let last = a.width().max(b.width()) - 1;
        let x = self.implies(b.bit(last), a.bit(last));
        cmp.add(x);
        let mut prev_equals = self.iff(a.bit(last), b.bit(last));
        let mut i = last - 1;
        while i >= 0 {
            let (v0, v1) = (a.bit(i), b.bit(i));
            let inner = self.implies(v0, v1);
            let x = self.implies(prev_equals, inner);
            cmp.add(x);
            let e = self.iff(v0, v1);
            prev_equals = self.and(prev_equals, e);
            i -= 1;
        }
        self.accumulate(&cmp)
    }
    pub fn int_lt(&mut self, a: &Int, b: &Int) -> BV {
        let leq = self.int_lte(a, b);
        let mut acc = Acc::new(Op::Or);
        let w = a.width().max(b.width());
        for i in 0..w {
            let x = self.xor(a.bit(i), b.bit(i));
            acc.add(x);
        }
        let ne = self.accumulate(&acc);
        self.and(leq, ne)
    }
    pub fn int_gt(&mut self, a: &Int, b: &Int) -> BV {
        self.int_lt(b, a)
    }
    pub fn int_gte(&mut self, a: &Int, b: &Int) -> BV {
        self.int_lte(b, a)
    }

    pub fn int_plus(&mut self, a: &Int, b: &Int) -> Int {
        let width = (a.width().max(b.width()) + 1).min(self.bitwidth);
        let mut plus = Vec::with_capacity(width as usize);
        let (mut carry, mut c1, mut c2) = (FALSE, FALSE, FALSE);
        for i in 0..width {
            let (v0, v1) = (a.bit(i), b.bit(i));
            plus.push(self.sum3(v0, v1, carry));
            carry = self.carry(v0, v1, carry);
            if i == width - 2 {
                c2 = carry;
            } else if i == width - 1 {
                c1 = carry;
            }
        }
        let overflow = if width == self.bitwidth { self.xor(c1, c2) } else { FALSE };
        let acc_of = self.merge_of(overflow, a.acc_of, b.acc_of);
        Int { bits: plus, of: overflow, acc_of }
    }

    pub fn int_minus(&mut self, a: &Int, b: &Int) -> Int {
        let width = (a.width().max(b.width()) + 1).min(self.bitwidth);
        let mut minus = Vec::with_capacity(width as usize);
        let (mut carry, mut c1, mut c2) = (TRUE, FALSE, FALSE);
        for i in 0..width {
            let (v0, v1) = (a.bit(i), -b.bit(i));
            minus.push(self.sum3(v0, v1, carry));
            carry = self.carry(v0, v1, carry);
            if i == width - 2 {
                c2 = carry;
            } else if i == width - 1 {
                c1 = carry;
            }
        }
        let overflow = if width == self.bitwidth { self.xor(c1, c2) } else { FALSE };
        let acc_of = self.merge_of(overflow, a.acc_of, b.acc_of);
        Int { bits: minus, of: overflow, acc_of }
    }

    fn add_and_carry(&mut self, bits: &mut [BV], index: usize, new_bit: BV, cin: BV) -> BV {
        let old = bits[index];
        bits[index] = self.sum3(old, new_bit, cin);
        self.carry(old, new_bit, cin)
    }

    pub fn int_multiply(&mut self, a: &Int, b: &Int) -> Int {
        let ret_width = (a.width() + b.width()) as usize;
        let mut mult = vec![FALSE; ret_width];
        let mut ibit = a.bit(0);
        for j in 0..ret_width {
            mult[j] = self.and(ibit, b.bit(j as i32));
        }
        let last = ret_width - 1;
        for i in 1..last {
            ibit = a.bit(i as i32);
            let mut carry = FALSE;
            for j in 0..ret_width - i {
                let bit = self.and(ibit, b.bit(j as i32));
                carry = self.add_and_carry(&mut mult, i + j, bit, carry);
            }
        }
        ibit = a.bit(last as i32);
        let mut carry = TRUE;
        for j in 0..ret_width - last {
            let bit = -self.and(ibit, b.bit(j as i32));
            carry = self.add_and_carry(&mut mult, last + j, bit, carry);
        }
        let width = mult.len().min(self.bitwidth as usize);
        let trunc: Vec<BV> = mult[..width].to_vec();
        let mut acc = Acc::new(Op::Or);
        for i in width..mult.len() {
            let x = self.xor(mult[i - 1], mult[i]);
            acc.add(x);
        }
        let overflow = self.accumulate(&acc);
        let acc_of = self.merge_of(overflow, a.acc_of, b.acc_of);
        Int { bits: trunc, of: overflow, acc_of }
    }

    fn extend_bits(a: &Int, extwidth: usize) -> Vec<BV> {
        let mut ext = a.bits.clone();
        let sign = *a.bits.last().unwrap();
        while ext.len() < extwidth {
            ext.push(sign);
        }
        ext.truncate(extwidth.max(a.bits.len()));
        ext
    }

    fn non_restoring_division(&mut self, a: &Int, d: &Int, quotient: bool) -> Vec<BV> {
        let width = self.bitwidth as usize;
        let extended = width * 2 + 1;
        let mut s = Self::extend_bits(a, extended);
        let mut q = vec![FALSE; width];
        let mut svalues = vec![FALSE; width];
        let dmsb = d.bit(width as i32);
        let mut sleft = 0usize;
        for i in 0..width {
            svalues[i] = self.tree_gate(Op::Or, &s);
            let sright = (sleft + extended - 1) % extended;
            let qbit = self.iff(s[sright], dmsb);
            q[width - i - 1] = qbit;
            s[sright] = FALSE;
            sleft = sright;
            let mut carry = qbit;
            let mut si = (sleft + width) % extended;
            for di in 0..=width {
                let dbit = self.xor(qbit, d.bit(di as i32));
                let sbit = s[si];
                s[si] = self.sum3(sbit, dbit, carry);
                carry = self.carry(sbit, dbit, carry);
                si = (si + 1) % extended;
            }
        }
        let all_s = self.tree_gate(Op::And, &svalues);
        let x1 = self.xor(s[width], a.bit(width as i32));
        let any_s = self.tree_gate(Op::Or, &s);
        let x2 = self.and(x1, any_s);
        let incorrect = self.or(-all_s, x2);
        let corrector = self.iff(s[width], d.bit(width as i32));
        if quotient {
            q.copy_within(0..width - 1, 1);
            q[0] = TRUE;
            let sign = self.and(incorrect, -corrector);
            let mut carry = self.and(incorrect, corrector);
            for i in 0..width {
                let qbit = q[i];
                q[i] = self.sum3(qbit, sign, carry);
                carry = self.carry(qbit, sign, carry);
            }
            q
        } else {
            let mut carry = self.and(incorrect, corrector);
            for i in 0..=width {
                let x = self.xor(corrector, d.bit(i as i32));
                let dbit = self.and(incorrect, x);
                let sbit = s[i];
                s[i] = self.sum3(sbit, dbit, carry);
                carry = self.carry(sbit, dbit, carry);
            }
            s[..width].to_vec()
        }
    }

    pub fn int_divide(&mut self, a: &Int, b: &Int) -> Int {
        let bits = self.non_restoring_division(a, b, true);
        let zero = self.integer(0);
        let div_by_zero = self.int_eq(b, &zero);
        let min = self.integer(-(1i32 << (self.bitwidth - 1)));
        let e1 = self.int_eq(a, &min);
        let m1 = self.integer(-1);
        let e2 = self.int_eq(b, &m1);
        let single = self.and(e1, e2);
        let overflow = self.or(div_by_zero, single);
        let acc_of = self.merge_of(overflow, a.acc_of, b.acc_of);
        Int { bits, of: overflow, acc_of }
    }

    pub fn int_modulo(&mut self, a: &Int, b: &Int) -> Int {
        let bits = self.non_restoring_division(a, b, false);
        let zero = self.integer(0);
        let div_by_zero = self.int_eq(b, &zero);
        let acc_of = self.merge_of(div_by_zero, a.acc_of, b.acc_of);
        Int { bits, of: FALSE, acc_of }
    }

    pub fn int_choice(&mut self, a: &Int, cond: BV, b: &Int) -> Int {
        let width = a.width().max(b.width());
        let mut bits = Vec::with_capacity(width as usize);
        for i in 0..width {
            bits.push(self.ite(cond, a.bit(i), b.bit(i)));
        }
        let of = self.ite(cond, a.of, b.of);
        let acc_of = self.ite(cond, a.acc_of, b.acc_of);
        Int { bits, of, acc_of }
    }

    fn int_bitwise(&mut self, a: &Int, b: &Int, op: u8) -> Int {
        let width = a.width().max(b.width());
        let mut bits = Vec::with_capacity(width as usize);
        for i in 0..width {
            bits.push(match op {
                0 => self.and(a.bit(i), b.bit(i)),
                1 => self.or(a.bit(i), b.bit(i)),
                _ => self.xor(a.bit(i), b.bit(i)),
            });
        }
        let acc_of = self.merge_of(FALSE, a.acc_of, b.acc_of);
        Int { bits, of: FALSE, acc_of }
    }
    pub fn int_and(&mut self, a: &Int, b: &Int) -> Int {
        self.int_bitwise(a, b, 0)
    }
    pub fn int_or(&mut self, a: &Int, b: &Int) -> Int {
        self.int_bitwise(a, b, 1)
    }
    pub fn int_xor(&mut self, a: &Int, b: &Int) -> Int {
        self.int_bitwise(a, b, 2)
    }

    pub fn int_shl(&mut self, a: &Int, b: &Int) -> Int {
        let width = self.bitwidth as usize;
        let mut sh = Int { bits: Self::extend_bits(a, width), of: FALSE, acc_of: FALSE };
        let max = 32 - ((width as u32 - 1).leading_zeros() as usize);
        let mut acc = Acc::new(Op::Or);
        for i in 0..width {
            let shift = 1usize << i;
            let bit = b.bit(i as i32);
            for x in 0..shift {
                let b1 = if (width as isize) - (x as isize) - 1 < 0 { FALSE } else { sh.bit((width - x - 1) as i32) };
                let b2 = if (width as isize) - (x as isize) - 2 < 0 { FALSE } else { sh.bit((width - x - 2) as i32) };
                let xx = self.xor(b1, b2);
                let v = self.ite(bit, xx, FALSE);
                acc.add(v);
            }
            if i < max {
                let mut j = width as isize - 1;
                while j >= 0 {
                    let ju = j as usize;
                    let t = if ju < shift { FALSE } else { sh.bit((ju - shift) as i32) };
                    sh.bits[ju] = self.ite(bit, t, sh.bits[ju]);
                    j -= 1;
                }
            }
        }
        let overflow = self.accumulate(&acc);
        let acc_of = self.merge_of(overflow, a.acc_of, b.acc_of);
        sh.of = overflow;
        sh.acc_of = acc_of;
        sh
    }

    fn int_shr_sign(&mut self, a: &Int, b: &Int, sign: BV) -> Int {
        let width = self.bitwidth as usize;
        let mut sh = Int { bits: Self::extend_bits(a, width), of: FALSE, acc_of: FALSE };
        let max = 32 - ((width as u32 - 1).leading_zeros() as usize);
        for i in 0..max {
            let shift = 1usize << i;
            let fill = width as isize - shift as isize;
            let bit = b.bit(i as i32);
            for j in 0..width {
                let t = if (j as isize) < fill { sh.bit((j + shift) as i32) } else { sign };
                sh.bits[j] = self.ite(bit, t, sh.bits[j]);
            }
        }
        sh.acc_of = self.merge_of(FALSE, a.acc_of, b.acc_of);
        sh
    }
    pub fn int_shr(&mut self, a: &Int, b: &Int) -> Int {
        self.int_shr_sign(a, b, FALSE)
    }
    pub fn int_sha(&mut self, a: &Int, b: &Int) -> Int {
        let sign = *a.bits.last().unwrap();
        self.int_shr_sign(a, b, sign)
    }
    pub fn int_negate(&mut self, a: &Int) -> Int {
        let zero = Int { bits: vec![FALSE], of: FALSE, acc_of: FALSE };
        self.int_minus(&zero, a)
    }
    pub fn int_not(&mut self, a: &Int) -> Int {
        Int { bits: a.bits.iter().map(|&b| -b).collect(), of: FALSE, acc_of: a.acc_of }
    }
    pub fn int_abs(&mut self, a: &Int) -> Int {
        let negated = self.int_negate(a);
        let msb = -*a.bits.last().unwrap();
        self.int_choice(a, msb, &negated)
    }
    pub fn int_sgn(&mut self, a: &Int) -> Int {
        let s0 = self.tree_gate(Op::Or, &a.bits);
        let s1 = *a.bits.last().unwrap();
        Int { bits: vec![s0, s1], of: FALSE, acc_of: a.acc_of }
    }

    /// `TwosComplementInt.apply(plus, others...)`: pairwise tree reduction.
    pub fn int_apply_nary(&mut self, plus: bool, first: &Int, others: &[Int]) -> Int {
        let mut ints: Vec<Int> = Vec::with_capacity(others.len() + 1);
        ints.push(first.clone());
        ints.extend(others.iter().cloned());
        let mut part = ints.len();
        while part > 1 {
            let max = part - 1;
            let mut i = 0;
            while i < max {
                let r = if plus { self.int_plus(&ints[i], &ints[i + 1]) } else { self.int_multiply(&ints[i], &ints[i + 1]) };
                ints[i / 2] = r;
                i += 2;
            }
            if max % 2 == 0 {
                ints[max / 2] = ints[max].clone();
            }
            part -= part / 2;
        }
        ints.swap_remove(0)
    }

    /// `TwosComplementInt.apply(Operator.Nary, others...)` (n-ary bitwise and/or).
    pub fn int_apply_bitwise(&mut self, op: Op, first: &Int, others: &[Int]) -> Int {
        let mut width = first.width();
        for o in others {
            width = width.max(o.width());
        }
        let sc = short_circuit(op);
        let mut bits = Vec::with_capacity(width as usize);
        for i in 0..width {
            let mut acc = Acc::new(op);
            acc.add(first.bit(i));
            for o in others {
                if acc.add(o.bit(i)) == sc {
                    break;
                }
            }
            bits.push(self.accumulate(&acc));
        }
        let mut ofs = vec![first.acc_of];
        ofs.extend(others.iter().map(|o| o.acc_of));
        let acc_of = self.tree_gate(op, &ofs);
        Int { bits, of: FALSE, acc_of }
    }

    /// `BooleanFactory.sum(Collection<BooleanValue>)`: balanced recursive sum of 1-bit integers.
    pub fn sum_bits(&mut self, bits: &[BV]) -> Int {
        let mut it = bits.iter().copied();
        self.sum_bits_rec(&mut it, 0, bits.len() as i32 - 1)
    }
    fn sum_bits_rec(&mut self, it: &mut dyn Iterator<Item = BV>, low: i32, high: i32) -> Int {
        if low > high {
            self.integer(0)
        } else if low == high {
            let v = it.next().unwrap();
            self.integer_bit(1, v)
        } else {
            let mid = (low + high) / 2;
            let l = self.sum_bits_rec(it, low, mid);
            let h = self.sum_bits_rec(it, mid + 1, high);
            self.int_plus(&l, &h)
        }
    }
}

/// `TwosComplementInt` (+ its `DefCond` overflow flags; `DefCond.vars` only matter with `noOverflow`).
#[derive(Clone, Debug)]
pub struct Int {
    pub bits: Vec<BV>,
    pub of: BV,
    pub acc_of: BV,
}

impl Int {
    pub fn width(&self) -> i32 {
        self.bits.len() as i32
    }
    pub fn bit(&self, i: i32) -> BV {
        self.bits[(i as usize).min(self.bits.len() - 1)]
    }
    pub fn is_constant(&self) -> bool {
        self.bits.iter().all(|&b| b == TRUE || b == FALSE)
    }
    pub fn value(&self) -> i32 {
        let max = self.bits.len() - 1;
        let mut ret = 0i32;
        for i in 0..max {
            if self.bits[i] == TRUE {
                ret = ret.wrapping_add(1 << i);
            }
        }
        if self.bits[max] == TRUE {
            ret = ret.wrapping_sub(1 << max);
        }
        ret
    }
    /// `twosComplementBits()` (bitwidth bits, sign-extended)
    pub fn twos_complement_bits(&self, bitwidth: i32) -> Vec<BV> {
        (0..bitwidth).map(|i| self.bit(i)).collect()
    }
}

// ---------------------------------------------------------------------------------------------- matrices

/// `Dimensions.square(size, n)` (the only shape the Alloy pipeline produces).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Dims {
    pub size: u32,
    pub n: u32,
}

impl Dims {
    pub fn square(size: u32, n: u32) -> Result<Dims, String> {
        let cap = (size as f64).powi(n as i32).round();
        if cap > i32::MAX as f64 || cap <= 0.0 {
            return Err(format!("Matrix too large: requested capacity of {cap}"));
        }
        Ok(Dims { size, n })
    }
    pub fn capacity(&self) -> u32 {
        self.size.pow(self.n)
    }
    pub fn dimension(&self, _i: usize) -> u32 {
        self.size
    }
    pub fn cross(&self, o: &Dims) -> Result<Dims, String> {
        Dims::square(self.size, self.n + o.n)
    }
    pub fn dot(&self, o: &Dims) -> Result<Dims, String> {
        let n = self.n + o.n - 2;
        if n == 0 {
            return Err("invalid join of two unary expressions".into());
        }
        Dims::square(self.size, n)
    }
}

/// `BooleanMatrix`: sorted cells (index -> value, never FALSE), plus its `DefCond` overflow flags.
#[derive(Clone, Debug)]
pub struct Matrix {
    pub dims: Dims,
    pub cells: BTreeMap<u32, BV>,
    pub of: BV,
    pub acc_of: BV,
}

enum DotCell {
    True,
    Acc(Acc),
}

impl Matrix {
    pub fn empty(dims: Dims) -> Matrix {
        Matrix { dims, cells: BTreeMap::new(), of: FALSE, acc_of: FALSE }
    }
    #[inline]
    pub fn get(&self, i: u32) -> BV {
        self.cells.get(&i).copied().unwrap_or(FALSE)
    }
    #[inline]
    pub fn fast_set(&mut self, i: u32, v: BV) {
        if v == FALSE {
            self.cells.remove(&i);
        } else {
            self.cells.insert(i, v);
        }
    }
    pub fn set(&mut self, i: u32, v: BV) {
        self.fast_set(i, v)
    }
    pub fn density(&self) -> usize {
        self.cells.len()
    }
}

impl Factory {
    /// `mergeDefConds(of=FALSE, bms...)` on a fresh matrix whose flags are FALSE.
    fn merge_dc(&mut self, cur_acc: BV, accs: &[BV]) -> BV {
        let mut r = self.or(FALSE, cur_acc);
        for &a in accs {
            r = self.or(r, a);
        }
        r
    }

    /// `BooleanMatrix.clone()`
    pub fn m_clone(&mut self, m: &Matrix) -> Matrix {
        let acc = self.merge_dc(FALSE, &[m.acc_of]);
        Matrix { dims: m.dims, cells: m.cells.clone(), of: FALSE, acc_of: acc }
    }

    pub fn m_not(&mut self, m: &Matrix) -> Matrix {
        let mut r = Matrix::empty(m.dims);
        r.acc_of = self.merge_dc(FALSE, &[m.acc_of]);
        for i in 0..m.dims.capacity() {
            match m.cells.get(&i) {
                None => {
                    r.cells.insert(i, TRUE);
                }
                Some(&v) if v != TRUE => {
                    r.cells.insert(i, -v);
                }
                _ => {}
            }
        }
        r
    }

    pub fn m_and(&mut self, a: &Matrix, b: &Matrix) -> Matrix {
        let mut r = Matrix::empty(a.dims);
        r.acc_of = self.merge_dc(FALSE, &[a.acc_of, b.acc_of]);
        if a.cells.is_empty() || b.cells.is_empty() {
            return r;
        }
        for (&i, &v0) in &a.cells {
            if let Some(&v1) = b.cells.get(&i) {
                let x = self.and(v0, v1);
                r.fast_set(i, x);
            }
        }
        r
    }

    /// `BooleanMatrix(d, m, rest...)` constructor flags: mergeDefConds(m) then mergeDefConds(rest)
    fn nary_flags(&mut self, first: &Matrix, rest: &[&Matrix]) -> BV {
        let a1 = self.merge_dc(FALSE, &[first.acc_of]);
        let accs: Vec<BV> = rest.iter().map(|m| m.acc_of).collect();
        self.merge_dc(a1, &accs)
    }

    pub fn m_and_n(&mut self, first: &Matrix, others: &[&Matrix]) -> Matrix {
        let mut r = Matrix::empty(first.dims);
        r.acc_of = self.nary_flags(first, others);
        for (&i, &v) in &first.cells {
            let mut acc = Acc::new(Op::And);
            acc.add(v);
            for o in others {
                if acc.add(o.get(i)) == FALSE {
                    break;
                }
            }
            if !acc.is_short_circuited() {
                let x = self.accumulate(&acc);
                r.fast_set(i, x);
            }
        }
        r
    }

    pub fn m_or(&mut self, a: &Matrix, b: &Matrix) -> Matrix {
        if a.cells.is_empty() {
            return self.m_clone(b);
        } else if b.cells.is_empty() {
            return self.m_clone(a);
        }
        let mut r = Matrix::empty(a.dims);
        r.acc_of = self.merge_dc(FALSE, &[a.acc_of, b.acc_of]);
        for (&i, &v0) in &a.cells {
            match b.cells.get(&i) {
                None => {
                    r.cells.insert(i, v0);
                }
                Some(&v1) => {
                    let x = self.or(v0, v1);
                    r.cells.insert(i, x);
                }
            }
        }
        for (&i, &v1) in &b.cells {
            if !a.cells.contains_key(&i) {
                r.cells.insert(i, v1);
            }
        }
        r
    }

    pub fn m_or_n(&mut self, first: &Matrix, others: &[&Matrix]) -> Matrix {
        let mut r = Matrix::empty(first.dims);
        r.acc_of = self.nary_flags(first, others);
        for (&i, &v) in &first.cells {
            let mut acc = Acc::new(Op::Or);
            acc.add(v);
            for o in others {
                if acc.add(o.get(i)) == TRUE {
                    break;
                }
            }
            let x = self.accumulate(&acc);
            r.fast_set(i, x);
        }
        for k in 0..others.len() {
            for (&i, &v) in &others[k].cells {
                if r.cells.contains_key(&i) {
                    continue;
                }
                let mut acc = Acc::new(Op::Or);
                acc.add(v);
                for o in &others[k + 1..] {
                    if acc.add(o.get(i)) == TRUE {
                        break;
                    }
                }
                let x = self.accumulate(&acc);
                r.fast_set(i, x);
            }
        }
        r
    }

    pub fn m_cross(&mut self, a: &Matrix, b: &Matrix) -> Result<Matrix, String> {
        let mut r = Matrix::empty(a.dims.cross(&b.dims)?);
        r.acc_of = self.merge_dc(FALSE, &[a.acc_of, b.acc_of]);
        if a.cells.is_empty() || b.cells.is_empty() {
            return Ok(r);
        }
        let ocap = b.dims.capacity();
        for (&i0, &v0) in &a.cells {
            let base = ocap * i0;
            for (&i1, &v1) in &b.cells {
                let c = self.and(v0, v1);
                if c != FALSE {
                    r.cells.insert(base + i1, c);
                }
            }
        }
        Ok(r)
    }

    pub fn m_cross_n(&mut self, first: &Matrix, others: &[&Matrix]) -> Result<Matrix, String> {
        let mut rd = first.dims;
        let mut empty = first.cells.is_empty();
        for o in others {
            rd = rd.cross(&o.dims)?;
            empty = empty || o.cells.is_empty();
        }
        let mut r = Matrix::empty(rd);
        r.acc_of = self.nary_flags(first, others);
        if empty {
            return Ok(r);
        }
        let ocap = rd.capacity() / first.dims.capacity();
        let idx_lists: Vec<Vec<u32>> = others.iter().map(|o| o.cells.keys().copied().collect()).collect();
        let caps: Vec<u32> = others.iter().map(|o| o.dims.capacity()).collect();
        for (&ci, &cv) in &first.cells {
            let base = ocap * ci;
            // odometer over the others' indices, last one fastest (initCross/nextCross)
            let mut pos = vec![0usize; others.len()];
            loop {
                let mut rest_idx = 0u32;
                let mut mult = 1u32;
                for k in (0..others.len()).rev() {
                    rest_idx += mult * idx_lists[k][pos[k]];
                    mult *= caps[k];
                }
                let mut acc = Acc::new(Op::And);
                acc.add(cv);
                for k in (0..others.len()).rev() {
                    if acc.add(others[k].get(idx_lists[k][pos[k]])) == FALSE {
                        break;
                    }
                }
                if !acc.is_short_circuited() {
                    let x = self.accumulate(&acc);
                    r.fast_set(base + rest_idx, x);
                }
                // advance
                let mut k = others.len();
                let mut done = true;
                while k > 0 {
                    k -= 1;
                    if pos[k] + 1 < idx_lists[k].len() {
                        pos[k] += 1;
                        done = false;
                        break;
                    } else {
                        pos[k] = 0;
                    }
                }
                if done {
                    break;
                }
            }
        }
        Ok(r)
    }

    pub fn m_dot(&mut self, a: &Matrix, b: &Matrix) -> Result<Matrix, String> {
        let mut r = Matrix::empty(a.dims.dot(&b.dims)?);
        r.acc_of = self.merge_dc(FALSE, &[a.acc_of, b.acc_of]);
        if a.cells.is_empty() || b.cells.is_empty() {
            return Ok(r);
        }
        let mut mutable: BTreeMap<u32, DotCell> = BTreeMap::new();
        let bd = b.dims.dimension(0);
        let c = b.dims.capacity() / bd;
        for (&i, &ival) in &a.cells {
            let row_head = (i % bd) * c;
            let row_tail = row_head + c - 1;
            for (&j, &jval) in b.cells.range(row_head..=row_tail) {
                let rv = self.and(ival, jval);
                if rv != FALSE {
                    let k = (i / bd) * c + j % c;
                    if rv == TRUE {
                        mutable.insert(k, DotCell::True);
                    } else {
                        match mutable.get_mut(&k) {
                            Some(DotCell::True) => {}
                            Some(DotCell::Acc(acc)) => {
                                acc.add(rv);
                            }
                            None => {
                                let mut acc = Acc::new(Op::Or);
                                acc.add(rv);
                                mutable.insert(k, DotCell::Acc(acc));
                            }
                        }
                    }
                }
            }
        }
        for (k, cell) in mutable {
            match cell {
                DotCell::True => r.fast_set(k, TRUE),
                DotCell::Acc(acc) => {
                    let x = self.accumulate(&acc);
                    r.fast_set(k, x);
                }
            }
        }
        Ok(r)
    }

    pub fn m_subset(&mut self, a: &Matrix, b: &Matrix) -> BV {
        let mut acc = Acc::new(Op::And);
        for (&i, &v) in &a.cells {
            let x = self.or(-v, b.get(i));
            if acc.add(x) == FALSE {
                return FALSE;
            }
        }
        self.accumulate(&acc)
    }

    pub fn m_eq(&mut self, a: &Matrix, b: &Matrix) -> BV {
        let x = self.m_subset(a, b);
        let y = self.m_subset(b, a);
        self.and(x, y)
    }

    pub fn m_difference(&mut self, a: &Matrix, b: &Matrix) -> Matrix {
        let mut r = Matrix::empty(a.dims);
        r.acc_of = self.merge_dc(FALSE, &[a.acc_of, b.acc_of]);
        for (&i, &v) in &a.cells {
            let x = self.and(v, -b.get(i));
            r.fast_set(i, x);
        }
        r
    }

    pub fn m_closure(&mut self, m: &Matrix) -> Result<Matrix, String> {
        if m.dims.n != 2 {
            return Err("closure of a non-binary relation".into());
        }
        if m.cells.is_empty() {
            return Ok(self.m_clone(m));
        }
        let row_factor = m.dims.size;
        let mut row_num = 0;
        let mut lead = m.cells.keys().next().copied();
        while let Some(l) = lead {
            row_num += 1;
            let next_row = ((l / row_factor) + 1) * row_factor;
            lead = m.cells.range(next_row..).next().map(|(k, _)| *k);
        }
        let mut ret: Option<Matrix> = None;
        let mut i = 1;
        while i < row_num {
            let cur = ret.as_ref().unwrap_or(m);
            let d = self.m_dot(cur, cur)?;
            let cur = ret.as_ref().unwrap_or(m);
            let o = self.m_or(cur, &d);
            ret = Some(o);
            i *= 2;
        }
        Ok(match ret {
            Some(r) => r,
            None => self.m_clone(m),
        })
    }

    pub fn m_transpose(&mut self, m: &Matrix) -> Matrix {
        let mut r = Matrix::empty(m.dims);
        r.acc_of = self.merge_dc(FALSE, &[m.acc_of]);
        let (rows, cols) = (m.dims.size, m.dims.size);
        for (&i, &v) in &m.cells {
            r.cells.insert((i % cols) * rows + (i / cols), v);
        }
        r
    }

    pub fn m_choice(&mut self, a: &Matrix, cond: BV, b: &Matrix) -> Matrix {
        if cond == TRUE {
            return self.m_clone(a);
        } else if cond == FALSE {
            return self.m_clone(b);
        }
        let mut r = Matrix::empty(a.dims);
        for (&i, &v0) in &a.cells {
            match b.cells.get(&i) {
                None => {
                    let x = self.and(cond, v0);
                    r.fast_set(i, x);
                }
                Some(&v1) => {
                    let x = self.ite(cond, v0, v1);
                    r.fast_set(i, x);
                }
            }
        }
        for (&i, &v1) in &b.cells {
            if !a.cells.contains_key(&i) {
                let x = self.and(-cond, v1);
                r.fast_set(i, x);
            }
        }
        r.of = self.ite(cond, a.of, b.of);
        r.acc_of = self.ite(cond, a.acc_of, b.acc_of);
        r
    }

    fn m_nand(&mut self, m: &Matrix, start: u32, end: u32) -> BV {
        let mut acc = Acc::new(Op::And);
        if end > start {
            for (_, &v) in m.cells.range(start..=end - 1) {
                if acc.add(-v) == FALSE {
                    return FALSE;
                }
            }
        }
        self.accumulate(&acc)
    }

    pub fn m_override(&mut self, a: &Matrix, b: &Matrix) -> Matrix {
        if b.cells.is_empty() {
            return self.m_clone(a);
        }
        let mut r = Matrix::empty(a.dims);
        r.acc_of = self.merge_dc(FALSE, &[a.acc_of, b.acc_of]);
        for (&i, &v) in &b.cells {
            r.cells.insert(i, v);
        }
        let row_len = a.dims.capacity() / a.dims.size;
        let mut row: i64 = -1;
        let mut row_val = TRUE;
        for (&i, &v0) in &a.cells {
            let e0row = (i / row_len) as i64;
            if row != e0row {
                row = e0row;
                row_val = self.m_nand(b, row as u32 * row_len, (row as u32 + 1) * row_len);
            }
            let cur = r.get(i);
            let x = self.and(v0, row_val);
            let y = self.or(cur, x);
            r.fast_set(i, y);
        }
        r
    }

    pub fn m_override_n(&mut self, first: &Matrix, others: &[&Matrix]) -> Matrix {
        if others.is_empty() {
            return self.m_clone(first);
        }
        let mut ms: Vec<Matrix> = Vec::with_capacity(others.len() + 1);
        ms.push(first.clone());
        ms.extend(others.iter().map(|m| (*m).clone()));
        let mut part = ms.len();
        while part > 1 {
            let max = part - 1;
            let mut i = 0;
            while i < max {
                let o = self.m_override(&ms[i], &ms[i + 1]);
                ms[i / 2] = o;
                i += 2;
            }
            if max % 2 == 0 {
                ms[max / 2] = ms[max].clone();
            }
            part -= part / 2;
        }
        ms.swap_remove(0)
    }

    pub fn m_cardinality(&mut self, m: &Matrix) -> Int {
        let vals: Vec<BV> = m.cells.values().copied().collect();
        let mut r = self.sum_bits(&vals);
        let x = self.or(FALSE, r.acc_of);
        r.acc_of = self.or(x, m.acc_of);
        r
    }

    pub fn m_some(&mut self, m: &Matrix) -> BV {
        let mut acc = Acc::new(Op::Or);
        for &v in m.cells.values() {
            if acc.add(v) == TRUE {
                return TRUE;
            }
        }
        self.accumulate(&acc)
    }

    pub fn m_lone(&mut self, m: &Matrix) -> BV {
        if m.cells.is_empty() {
            return TRUE;
        }
        let mut acc = Acc::new(Op::And);
        let mut partial = FALSE;
        for &v in m.cells.values() {
            let x = self.or(-v, -partial);
            if acc.add(x) == FALSE {
                return FALSE;
            }
            partial = self.or(partial, v);
        }
        self.accumulate(&acc)
    }

    pub fn m_one(&mut self, m: &Matrix) -> BV {
        if m.cells.is_empty() {
            return FALSE;
        }
        let mut acc = Acc::new(Op::And);
        let mut partial = FALSE;
        for &v in m.cells.values() {
            let x = self.or(-v, -partial);
            if acc.add(x) == FALSE {
                return FALSE;
            }
            partial = self.or(partial, v);
        }
        acc.add(partial);
        self.accumulate(&acc)
    }

    pub fn m_none(&mut self, m: &Matrix) -> BV {
        -self.m_some(m)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn super_fast_hash_matches_java() {
        // values computed with kodkod.util.ints.Ints.superFastHash on the JVM
        assert_eq!(super_fast_hash(1), super_fast_hash(1));
        assert_ne!(super_fast_hash(1), super_fast_hash(2));
    }

    #[test]
    fn and_or_simplify() {
        let mut f = Factory::new(3, 3, 4, false);
        assert_eq!(f.and(1, TRUE), 1);
        assert_eq!(f.and(1, FALSE), FALSE);
        assert_eq!(f.and(1, -1), FALSE);
        let g = f.and(1, 2);
        assert_eq!(g, 4);
        assert_eq!(f.and(2, 1), 4);
        assert_eq!(f.and(g, 1), g);
        assert_eq!(f.or(g, 1), 1);
    }
}
