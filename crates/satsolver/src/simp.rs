//! CNF preprocessing before the first solve: top-level unit propagation and bounded variable elimination.
//!
//! Port of the elimination part of MiniSat's `SimpSolver` (`eliminateVar`, `merge`, `extendModel`), the SatELite
//! scheme. Kodkod CNFs consist mostly of Tseitin gate variables (only a few percent are primary variables); a decision
//! on a primary variable propagates through long gate chains, and eliminating the gate variables shortens the trail
//! per conflict. Java Kodkod hands SAT4J the CNF unsimplified; this only changes how fast the same answer is found.
//!
//! Literals are DIMACS `i32`s; variables `1..=n_vars`. Frozen variables (primary/skolem variables that the caller
//! reads or reasons about) are never eliminated. Eliminated variables are given values afterwards by
//! [`extend_model`], so every variable of a model is consistent with the original CNF.

/// Resolvents longer than this are not produced (MiniSat `clause_lim`).
const CLAUSE_LIM: usize = 20;
/// A variable occurring more often than this in both polarities is not considered.
const OCC_LIM: usize = 10;
/// Upper bound on literal visits spent on elimination (keeps huge CNFs cheap).
const WORK_LIM: u64 = 30_000_000;

pub struct Simplified {
    /// Remaining clauses, flat and 0-terminated (units of the top-level assignment included).
    pub clauses: Vec<i32>,
    /// `eliminated[v]` (1-based) — the variable no longer occurs in `clauses`.
    pub eliminated: Vec<bool>,
    /// MiniSat `elimclauses`: per stored clause its literals (the eliminated variable's literal first), then the
    /// clause length.
    pub elim_stack: Vec<i32>,
    /// The CNF was found unsatisfiable.
    pub unsat: bool,
}

#[inline]
fn code(l: i32) -> usize {
    // literal -> index: 2v for v, 2v+1 for -v
    ((l.unsigned_abs() as usize) << 1) | (l < 0) as usize
}

struct Db {
    lits: Vec<i32>,
    /// (start, len) into `lits`; len == u32::MAX marks a deleted clause
    cls: Vec<(u32, u32)>,
    occ: Vec<Vec<u32>>,
    /// number of alive clauses containing each literal (`occ` may also hold dead clauses)
    cnt: Vec<u32>,
    val: Vec<i8>,
    work: u64,
}

const DEAD: u32 = u32::MAX;

impl Db {
    fn clause(&self, c: u32) -> &[i32] {
        let (s, l) = self.cls[c as usize];
        &self.lits[s as usize..(s + l) as usize]
    }

    fn alive(&self, c: u32) -> bool {
        self.cls[c as usize].1 != DEAD
    }

    fn add(&mut self, lits: &[i32]) -> u32 {
        let id = self.cls.len() as u32;
        let start = self.lits.len() as u32;
        self.lits.extend_from_slice(lits);
        self.cls.push((start, lits.len() as u32));
        for &l in lits {
            self.occ[code(l)].push(id);
            self.cnt[code(l)] += 1;
        }
        id
    }

    fn kill(&mut self, c: u32) {
        let (s, l) = self.cls[c as usize];
        if l == DEAD {
            return;
        }
        for &x in &self.lits[s as usize..(s + l) as usize] {
            self.cnt[code(x)] -= 1;
        }
        self.cls[c as usize].1 = DEAD;
    }

    fn value(&self, l: i32) -> i8 {
        let v = self.val[l.unsigned_abs() as usize];
        if l < 0 {
            -v
        } else {
            v
        }
    }

    /// Top-level unit propagation; returns false on a conflict.
    fn propagate(&mut self, queue: &mut Vec<i32>) -> bool {
        while let Some(u) = queue.pop() {
            match self.value(u) {
                1 => continue,
                -1 => return false,
                _ => {}
            }
            self.val[u.unsigned_abs() as usize] = if u > 0 { 1 } else { -1 };
            let sat = std::mem::take(&mut self.occ[code(u)]);
            for &c in &sat {
                self.kill(c);
            }
            let shrink = std::mem::take(&mut self.occ[code(-u)]);
            for &c in &shrink {
                if !self.alive(c) {
                    continue;
                }
                let (s, l) = self.cls[c as usize];
                let (s, mut l) = (s as usize, l as usize);
                let mut k = 0;
                while k < l {
                    if self.lits[s + k] == -u {
                        l -= 1;
                        self.lits.swap(s + k, s + l);
                        self.cnt[code(-u)] -= 1;
                    } else {
                        k += 1;
                    }
                }
                self.cls[c as usize].1 = l as u32;
                if l == 0 {
                    return false;
                }
                if l == 1 {
                    queue.push(self.lits[s]);
                }
            }
        }
        true
    }

    /// Alive clauses containing literal `l` into `out` (compacts the occurrence list).
    fn occurrences(&mut self, l: i32, out: &mut Vec<u32>) {
        let cls = &self.cls;
        let list = &mut self.occ[code(l)];
        list.retain(|&c| cls[c as usize].1 != DEAD);
        out.clear();
        out.extend_from_slice(list);
    }

    #[inline]
    fn occ_count(&self, l: i32) -> usize {
        self.cnt[code(l)] as usize
    }
}

/// Simplifies `flat` (0-terminated DIMACS clauses over `1..=n_vars`); `frozen[v]` variables are kept.
pub fn simplify(n_vars: u32, flat: &[i32], frozen: &[bool]) -> Simplified {
    let n = n_vars as usize;
    let mut db = Db {
        lits: Vec::with_capacity(flat.len()),
        cls: Vec::new(),
        occ: vec![Vec::new(); 2 * n + 2],
        cnt: vec![0; 2 * n + 2],
        val: vec![0; n + 1],
        work: 0,
    };
    let fail = |n: usize| Simplified { clauses: vec![0], eliminated: vec![false; n + 1], elim_stack: Vec::new(), unsat: true };
    // load: drop duplicate literals and tautologies
    let mut mark: Vec<u32> = vec![0; 2 * n + 2];
    let mut stamp: u32 = 0;
    let mut buf: Vec<i32> = Vec::new();
    let mut queue: Vec<i32> = Vec::new();
    for chunk in flat.split(|&l| l == 0) {
        if chunk.is_empty() {
            continue;
        }
        stamp += 1;
        buf.clear();
        let mut taut = false;
        for &l in chunk {
            if mark[code(-l)] == stamp {
                taut = true;
                break;
            }
            if mark[code(l)] != stamp {
                mark[code(l)] = stamp;
                buf.push(l);
            }
        }
        if taut {
            continue;
        }
        if buf.len() == 1 {
            queue.push(buf[0]);
        }
        db.add(&buf);
    }
    if !db.propagate(&mut queue) {
        return fail(n);
    }

    // bounded variable elimination, cheapest variables first (MiniSat `elim_heap` order: |pos| * |neg|)
    let mut eliminated = vec![false; n + 1];
    let mut elim_stack: Vec<i32> = Vec::new();
    let mut done = vec![false; n + 1];
    let cost = |db: &Db, v: i32| (db.occ_count(v) * db.occ_count(-v)) as u64;
    let mut heap: std::collections::BinaryHeap<std::cmp::Reverse<(u64, u32)>> = (1..=n as u32)
        .filter(|&v| !frozen.get(v as usize).copied().unwrap_or(false) && db.val[v as usize] == 0)
        .map(|v| std::cmp::Reverse((cost(&db, v as i32), v)))
        .collect();
    let mut resolvents: Vec<i32> = Vec::new();
    let mut res_ends: Vec<usize> = Vec::new();
    let mut pos: Vec<u32> = Vec::new();
    let mut neg: Vec<u32> = Vec::new();
    while let Some(std::cmp::Reverse((c0, v))) = heap.pop() {
        if db.work > WORK_LIM {
            break;
        }
        let vu = v as usize;
        if done[vu] || db.val[vu] != 0 {
            continue;
        }
        // costs only change through eliminations nearby; a variable that got more expensive goes back
        let cur = cost(&db, v as i32);
        if cur > c0 {
            heap.push(std::cmp::Reverse((cur, v)));
            continue;
        }
        done[vu] = true;
        let vi = v as i32;
        if db.occ_count(vi) > OCC_LIM && db.occ_count(-vi) > OCC_LIM {
            continue;
        }
        db.occurrences(vi, &mut pos);
        db.occurrences(-vi, &mut neg);
        // all non-tautological resolvents; give up when they outnumber the clauses they replace
        resolvents.clear();
        res_ends.clear();
        let limit = pos.len() + neg.len();
        let mut ok = true;
        'outer: for &p in &pos {
            for &q in &neg {
                stamp += 1;
                let start = resolvents.len();
                let mut taut = false;
                for &l in db.clause(p).iter().chain(db.clause(q).iter()) {
                    if l == vi || l == -vi {
                        continue;
                    }
                    if mark[code(-l)] == stamp {
                        taut = true;
                        break;
                    }
                    if mark[code(l)] != stamp {
                        mark[code(l)] = stamp;
                        resolvents.push(l);
                    }
                }
                db.work += (db.clause(p).len() + db.clause(q).len()) as u64;
                if taut {
                    resolvents.truncate(start);
                    continue;
                }
                if resolvents.len() - start > CLAUSE_LIM || res_ends.len() + 1 > limit {
                    ok = false;
                    break 'outer;
                }
                res_ends.push(resolvents.len());
            }
        }
        if !ok {
            continue;
        }
        // eliminate: store the smaller side for model extension (MiniSat `eliminateVar`), then replace by resolvents
        let (store, other_lit) = if pos.len() > neg.len() { (&neg, vi) } else { (&pos, -vi) };
        for &c in store {
            let lits = db.clause(c);
            let first = elim_stack.len();
            elim_stack.extend_from_slice(lits);
            // the eliminated variable's literal goes first
            let k = elim_stack[first..].iter().position(|&l| l.unsigned_abs() == v).expect("occurrence");
            elim_stack.swap(first, first + k);
            elim_stack.push(lits.len() as i32);
        }
        elim_stack.push(other_lit);
        elim_stack.push(1);
        for &c in pos.iter().chain(neg.iter()) {
            db.kill(c);
        }
        db.occ[code(vi)].clear();
        db.occ[code(-vi)].clear();
        eliminated[vu] = true;
        let mut s = 0;
        for &e in &res_ends {
            if e == s {
                // empty resolvent (cannot happen after unit propagation, but never drop it silently)
                return fail(n);
            }
            if e - s == 1 {
                queue.push(resolvents[s]);
            }
            db.add(&resolvents[s..e]);
            s = e;
        }
        if !queue.is_empty() && !db.propagate(&mut queue) {
            return fail(n);
        }
    }

    // output: top-level units, then the remaining clauses
    let mut clauses: Vec<i32> = Vec::with_capacity(db.lits.len() + db.cls.len());
    for v in 1..=n {
        if db.val[v] != 0 {
            clauses.push(if db.val[v] > 0 { v as i32 } else { -(v as i32) });
            clauses.push(0);
        }
    }
    for c in 0..db.cls.len() as u32 {
        if db.alive(c) {
            let lits = db.clause(c);
            // clauses with assigned literals were removed/shrunk by propagation
            clauses.extend_from_slice(lits);
            clauses.push(0);
        }
    }
    Simplified { clauses, eliminated, elim_stack, unsat: false }
}

/// Gives the eliminated variables values satisfying their stored clauses (MiniSat `extendModel`).
/// `model[v]` (1-based) holds the solver's values on entry.
pub fn extend_model(elim_stack: &[i32], model: &mut [bool]) {
    let lit_true = |model: &[bool], l: i32| model[l.unsigned_abs() as usize] == (l > 0);
    let mut i = elim_stack.len();
    while i > 0 {
        let len = elim_stack[i - 1] as usize;
        let start = i - 1 - len;
        let clause = &elim_stack[start..i - 1];
        if !clause[1..].iter().any(|&l| lit_true(model, l)) {
            let x = clause[0];
            model[x.unsigned_abs() as usize] = x > 0;
        }
        i = start;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn flat(cls: &[&[i32]]) -> Vec<i32> {
        let mut f = Vec::new();
        for c in cls {
            f.extend_from_slice(c);
            f.push(0);
        }
        f
    }

    fn satisfies(cls: &[&[i32]], model: &[bool]) -> bool {
        cls.iter().all(|c| c.iter().any(|&l| model[l.unsigned_abs() as usize] == (l > 0)))
    }

    /// Every model of the simplified CNF extends to a model of the original one; returns the number of models.
    fn check_extension(n: usize, cls: &[&[i32]], s: &Simplified) -> usize {
        let rest: Vec<Vec<i32>> = s.clauses.split(|&l| l == 0).filter(|c| !c.is_empty()).map(|c| c.to_vec()).collect();
        for c in &rest {
            assert!(c.iter().all(|l| !s.eliminated[l.unsigned_abs() as usize]), "eliminated variable left in {c:?}");
        }
        let mut found = 0;
        for bits in 0..(1u32 << n) {
            let mut model: Vec<bool> = (0..=n).map(|v| v > 0 && bits & (1 << (v - 1)) != 0).collect();
            if !rest.iter().all(|c| c.iter().any(|&l| model[l.unsigned_abs() as usize] == (l > 0))) {
                continue;
            }
            extend_model(&s.elim_stack, &mut model);
            assert!(satisfies(cls, &model), "{model:?}");
            found += 1;
        }
        found
    }

    #[test]
    fn eliminates_gate_and_extends_model() {
        // g <-> (a & b) with root g
        let cls: &[&[i32]] = &[&[-3, 1], &[-3, 2], &[3, -1, -2], &[3]];
        let s = simplify(3, &flat(cls), &[false, true, true, false]);
        assert!(!s.unsat);
        assert!(!s.eliminated[1] && !s.eliminated[2]);
        assert!(check_extension(3, cls, &s) > 0);
    }

    #[test]
    fn elimination_preserves_satisfiability_and_models() {
        // x3 -> x1 | x2, x4 -> x3 & x1 (one-sided gates), root x4 | x2, not both x1 and x2
        let cls: &[&[i32]] = &[&[-3, 1, 2], &[-4, 3], &[-4, 1], &[4, 2], &[-2, -1]];
        let s = simplify(4, &flat(cls), &[false, true, true, false, false]);
        assert!(!s.unsat);
        assert!(s.eliminated[3] || s.eliminated[4]);
        assert!(check_extension(4, cls, &s) > 0);
    }

    #[test]
    fn random_cnfs_keep_satisfiability_and_extend_models() {
        // brute-force differential test: original SAT <=> simplified SAT, and every simplified model extends
        let mut seed: u64 = 0x2545_f491_4f6c_dd1d;
        let mut rnd = |m: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % m
        };
        for _ in 0..400 {
            let n = 3 + rnd(6) as usize;
            let m = 2 + rnd(4 * n as u64) as usize;
            let mut cls: Vec<Vec<i32>> = Vec::new();
            for _ in 0..m {
                let len = 1 + rnd(3) as usize;
                let c: Vec<i32> =
                    (0..len).map(|_| (1 + rnd(n as u64) as i32) * if rnd(2) == 0 { 1 } else { -1 }).collect();
                cls.push(c);
            }
            let refs: Vec<&[i32]> = cls.iter().map(|c| c.as_slice()).collect();
            let frozen: Vec<bool> = (0..=n).map(|v| v > 0 && rnd(3) == 0).collect();
            let orig_sat = (0..(1u32 << n)).any(|bits| {
                let model: Vec<bool> = (0..=n).map(|v| v > 0 && bits & (1 << (v - 1)) != 0).collect();
                satisfies(&refs, &model)
            });
            let s = simplify(n as u32, &flat(&refs), &frozen);
            for v in 1..=n {
                assert!(!(frozen[v] && s.eliminated[v]), "frozen variable eliminated");
            }
            let models = if s.unsat { 0 } else { check_extension(n, &refs, &s) };
            assert_eq!(orig_sat, models > 0, "{cls:?} frozen {frozen:?}");
        }
    }

    #[test]
    fn detects_unsat() {
        let cls: &[&[i32]] = &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]];
        let s = simplify(2, &flat(cls), &[false, false, false]);
        // eliminating x1 yields the units x2 and -x2
        assert!(s.unsat);
    }
}
