//! Port of SAT4J 2.3.1 (`org.sat4j.core`, the version embedded in Alloy 6.2.0), configuration
//! `org.sat4j.minisat.SolverFactory.newDefault()` = `newMiniLearningHeapRsatExpSimpBiere()`:
//! `Solver<MixedDataStructureDanielWL>` + `MiniSATLearning` + `VarOrderHeap(RSATPhaseSelectionStrategy)` +
//! `ArminRestarts` + `SearchParams(1.1, 100)` + `EXPENSIVE_SIMPLIFICATION` + the `glucose` learned-clause deletion,
//! wrapped like `kodkod.solvers.SAT4J`.
//!
//! The port is meant to be *bit-exact*: for the same sequence of `add_variables`/`add_clause` calls it makes the same
//! decisions, propagations, learned clauses, restarts and clause-database reductions as the Java solver, so it finds
//! the same first model. Every ordering detail matters (watch-list order, `Vec.remove` shifting, `Vec.delete`
//! swapping, SAT4J's own quicksort, heap tie-breaking), so keep the Java structure when editing.
//!
//! Java sources: `org/sat4j/minisat/core/Solver.java`, `.../constraints/MixedDataStructureDanielWL.java`,
//! `.../constraints/cnf/{Clauses,Lits,UnitClause,BinaryClause,WLClause,...}.java`, `.../orders/VarOrderHeap.java`,
//! `.../core/Heap.java`, `.../restarts/ArminRestarts.java`, `org/sat4j/core/{Vec,VecInt}.java`.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

const NONE: u32 = u32::MAX;
/// `ILits.UNDEFINED`
const UNDEFINED: u32 = u32::MAX;
const VAR_RESCALE_FACTOR: f64 = 1e-100;
const VAR_RESCALE_BOUND: f64 = 1.0 / VAR_RESCALE_FACTOR;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Unit,
    Bin,
    Wl,
}

/// A constraint (Java `Constr`): `UnitClause`, `{Original,Learnt}BinaryClause` (`lits = [head, tail]`) or
/// `{Original,Learnt}WLClause`.
struct Constr {
    kind: Kind,
    learnt: bool,
    activity: f64,
    lits: Vec<u32>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Lbool {
    True,
    False,
    Undefined,
}

/// `org.sat4j.minisat.core.Heap` (1-based binary max-heap on activity; ties never move).
struct Heap {
    heap: Vec<u32>,
    indices: Vec<u32>,
}

impl Heap {
    fn new(size: usize) -> Heap {
        // Java: heap.push(-1); setBounds(size) = indices.growTo(size, 0)
        Heap { heap: vec![u32::MAX], indices: vec![0; size] }
    }
    #[inline]
    fn comp(act: &[f64], a: u32, b: u32) -> bool {
        act[a as usize] > act[b as usize]
    }
    fn percolate_up(&mut self, act: &[f64], mut i: usize) {
        let x = self.heap[i];
        while (i >> 1) != 0 && Self::comp(act, x, self.heap[i >> 1]) {
            self.heap[i] = self.heap[i >> 1];
            self.indices[self.heap[i] as usize] = i as u32;
            i >>= 1;
        }
        self.heap[i] = x;
        self.indices[x as usize] = i as u32;
    }
    fn percolate_down(&mut self, act: &[f64], mut i: usize) {
        let x = self.heap[i];
        let n = self.heap.len();
        while (i << 1) < n {
            let l = i << 1;
            let r = (i << 1) ^ 1;
            let child = if r < n && Self::comp(act, self.heap[r], self.heap[l]) { r } else { l };
            if !Self::comp(act, self.heap[child], x) {
                break;
            }
            self.heap[i] = self.heap[child];
            self.indices[self.heap[i] as usize] = i as u32;
            i = child;
        }
        self.heap[i] = x;
        self.indices[x as usize] = i as u32;
    }
    #[inline]
    fn in_heap(&self, n: u32) -> bool {
        self.indices[n as usize] != 0
    }
    #[inline]
    fn empty(&self) -> bool {
        self.heap.len() == 1
    }
    fn insert(&mut self, act: &[f64], n: u32) {
        self.indices[n as usize] = self.heap.len() as u32;
        self.heap.push(n);
        let i = self.indices[n as usize] as usize;
        self.percolate_up(act, i);
    }
    fn getmin(&mut self, act: &[f64]) -> u32 {
        let r = self.heap[1];
        let last = *self.heap.last().unwrap();
        self.heap[1] = last;
        self.indices[self.heap[1] as usize] = 1;
        self.indices[r as usize] = 0;
        self.heap.pop();
        if self.heap.len() > 1 {
            self.percolate_down(act, 1);
        }
        r
    }
}

/// Java `Math.round(double)` (half rounds towards positive infinity), as a long.
fn java_round(x: f64) -> i64 {
    let f = x.floor();
    if x - f == 0.5 {
        (f + 1.0) as i64
    } else {
        x.round() as i64
    }
}

/// SAT4J 2.3.1 default solver behind Kodkod's `SAT4J` wrapper.
pub struct Sat4j {
    // ---- Lits (vocabulary)
    pool: Vec<bool>,
    realn_vars: usize,
    maxvarid: usize,
    watches: Vec<Vec<u32>>,
    level: Vec<i32>,
    reason: Vec<u32>,
    falsified: Vec<bool>,
    // ---- Solver
    arena: Vec<Constr>,
    constrs: Vec<u32>,
    learnts: Vec<u32>,
    cla_inc: f64,
    cla_decay: f64,
    qhead: usize,
    trail: Vec<u32>,
    trail_lim: Vec<usize>,
    root_level: usize,
    declared_max_var_id: usize,
    seen: Vec<bool>,
    seen_dirty: Vec<u32>,
    out_learnt: Vec<u32>,
    preason: Vec<u32>,
    analyzetoclear: Vec<u32>,
    analyzestack: Vec<u32>,
    watched: Vec<u32>,
    need_to_reduce_db: bool,
    // ---- VarOrderHeap + RSAT phase
    activity: Vec<f64>,
    var_decay: f64,
    var_inc: f64,
    heap: Heap,
    phase: Vec<u32>,
    // ---- ArminRestarts (SearchParams(0.95, 0.999, 1.1, 100))
    inner: f64,
    outer: f64,
    restart_conflicts: i64,
    // ---- glucose deletion strategy + its ConflictTimerAdapter(1000)
    flags: Vec<i32>,
    flag: i32,
    wall: i32,
    cm_counter: i32,
    nbconflict: i32,
    nextbound: i32,
    // ---- result
    user_model: Vec<bool>,
    // ---- kodkod.solvers.SAT4J wrapper
    vars: u32,
    clauses: u64,
    sat: Option<bool>,
    stop: Option<Arc<AtomicBool>>,
}

const VAR_DECAY: f64 = 0.95;
const CLA_DECAY: f64 = 0.999;
const CONFLICT_BOUND_INC: f64 = 1.1;
const INIT_CONFLICT_BOUND: f64 = 100.0;

impl Default for Sat4j {
    fn default() -> Self {
        Self::new()
    }
}

impl Sat4j {
    pub fn new() -> Sat4j {
        Sat4j {
            pool: vec![false; 1],
            realn_vars: 0,
            maxvarid: 0,
            watches: vec![Vec::new(); 2],
            level: vec![-1; 1],
            reason: vec![NONE; 1],
            falsified: vec![false; 2],
            arena: Vec::new(),
            constrs: Vec::new(),
            learnts: Vec::new(),
            cla_inc: 1.0,
            cla_decay: 1.0,
            qhead: 0,
            trail: Vec::new(),
            trail_lim: Vec::new(),
            root_level: 0,
            declared_max_var_id: 0,
            seen: Vec::new(),
            seen_dirty: Vec::new(),
            out_learnt: Vec::new(),
            preason: Vec::new(),
            analyzetoclear: Vec::new(),
            analyzestack: Vec::new(),
            watched: Vec::new(),
            need_to_reduce_db: false,
            activity: vec![0.0; 1],
            var_decay: 1.0,
            var_inc: 1.0,
            heap: Heap::new(1),
            phase: Vec::new(),
            inner: 0.0,
            outer: 0.0,
            restart_conflicts: 0,
            flags: Vec::new(),
            flag: 0,
            wall: 0,
            cm_counter: 0,
            nbconflict: 0,
            nextbound: 5000,
            user_model: Vec::new(),
            vars: 0,
            clauses: 0,
            sat: None,
            stop: None,
        }
    }

    /// Abort the search (`solve` returns `None`) once `flag` is set.
    pub fn set_stop_flag(&mut self, flag: Arc<AtomicBool>) {
        self.stop = Some(flag);
    }

    // ------------------------------------------------------------------ Lits

    fn grow(&mut self, var: usize) {
        if var >= self.pool.len() {
            let n = var + 1;
            self.pool.resize(n, false);
            self.level.resize(n, -1);
            self.reason.resize(n, NONE);
            self.watches.resize_with(2 * n, Vec::new);
            self.falsified.resize(2 * n, false);
        }
    }

    // Java: Lits.getFromPool
    fn get_from_pool(&mut self, x: i32) -> u32 {
        let var = x.unsigned_abs() as usize;
        self.grow(var);
        if var > self.maxvarid {
            self.maxvarid = var;
        }
        let lit = if x < 0 { ((var as u32) << 1) ^ 1 } else { (var as u32) << 1 };
        if !self.pool[var] {
            self.realn_vars += 1;
            self.pool[var] = true;
            self.watches[var << 1].clear();
            self.watches[(var << 1) | 1].clear();
            self.level[var] = -1;
            self.falsified[var << 1] = false;
            self.falsified[(var << 1) | 1] = false;
        }
        lit
    }

    // Java: Lits.ensurePool
    fn ensure_pool(&mut self, howmany: usize) {
        self.grow(howmany);
        self.maxvarid = howmany;
    }

    #[inline]
    fn is_satisfied(&self, lit: u32) -> bool {
        self.falsified[(lit ^ 1) as usize]
    }
    #[inline]
    fn is_falsified(&self, lit: u32) -> bool {
        self.falsified[lit as usize]
    }
    #[inline]
    fn is_unassigned(&self, lit: u32) -> bool {
        !self.falsified[lit as usize] && !self.falsified[(lit ^ 1) as usize]
    }
    #[inline]
    fn get_level(&self, lit: u32) -> i32 {
        self.level[(lit >> 1) as usize]
    }
    #[inline]
    fn get_reason(&self, lit: u32) -> u32 {
        self.reason[(lit >> 1) as usize]
    }

    // ------------------------------------------------------------------ Kodkod SAT4J wrapper

    pub fn num_vars(&self) -> u32 {
        self.vars
    }
    pub fn num_clauses(&self) -> u64 {
        self.clauses
    }

    /// `SAT4J.addVariables`: `vars += n; solver.newVar(vars)`.
    pub fn add_variables(&mut self, n: u32) {
        if n > 0 {
            self.vars += n;
            // Solver.newVar(howmany)
            self.ensure_pool(self.vars as usize);
            self.declared_max_var_id = self.vars as usize;
        }
    }

    /// `SAT4J.addClause`: false once the problem is known UNSAT.
    pub fn add_clause(&mut self, lits: &[i32]) -> bool {
        if self.sat == Some(false) {
            return false;
        }
        self.clauses += 1;
        if self.add_clause_internal(lits).is_err() {
            self.sat = Some(false);
            return false;
        }
        true
    }

    /// `SAT4J.solve`: `Some(sat)`, or `None` if the stop flag aborted the search.
    pub fn solve(&mut self) -> Option<bool> {
        if self.sat == Some(false) {
            return Some(false);
        }
        let r = self.is_satisfiable();
        if let Some(b) = r {
            self.sat = Some(b);
        }
        r
    }

    /// `SAT4J.valueOf` (`Solver.model(var)`): false for variables never mentioned in a clause.
    pub fn value_of(&self, var: u32) -> bool {
        self.user_model.get(var as usize - 1).copied().unwrap_or(false)
    }

    // ------------------------------------------------------------------ clause creation

    // Java: Solver.addClause -> dimacs2internal -> MixedDataStructureDanielWL.createClause -> addConstr
    fn add_clause_internal(&mut self, dimacs: &[i32]) -> Result<(), ()> {
        let mut ps: Vec<u32> = Vec::with_capacity(dimacs.len());
        for &p in dimacs {
            ps.push(self.get_from_pool(p));
        }
        // Clauses.sanityCheck
        let mut i = 0;
        while i < ps.len() {
            if self.is_unassigned(ps[i]) {
                i += 1;
            } else {
                if self.is_satisfied(ps[i]) {
                    return Ok(()); // satisfied: ignored
                }
                // VecInt.delete(i): the last element moves to i
                let last = ps.pop().unwrap();
                if i < ps.len() {
                    ps[i] = last;
                }
            }
        }
        ps.sort_unstable();
        ps.dedup();
        for k in 0..ps.len().saturating_sub(1) {
            if ps[k] == (ps[k + 1] ^ 1) {
                return Ok(()); // tautology
            }
        }
        // propagationCheck
        if ps.is_empty() {
            return Err(());
        }
        if ps.len() == 1 {
            if !self.enqueue(ps[0], NONE) {
                return Err(());
            }
            let id = self.new_constr(Kind::Unit, false, ps);
            self.constrs.push(id);
            return Ok(());
        }
        let kind = if ps.len() == 2 { Kind::Bin } else { Kind::Wl };
        let (w0, w1) = (ps[0] ^ 1, ps[1] ^ 1);
        let id = self.new_constr(kind, false, ps);
        // register(): watch neg(lits[0]), neg(lits[1])
        self.watches[w0 as usize].push(id);
        self.watches[w1 as usize].push(id);
        self.constrs.push(id);
        Ok(())
    }

    fn new_constr(&mut self, kind: Kind, learnt: bool, lits: Vec<u32>) -> u32 {
        let id = self.arena.len() as u32;
        self.arena.push(Constr { kind, learnt, activity: 0.0, lits });
        id
    }

    // ------------------------------------------------------------------ trail

    #[inline]
    fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    // Java: Solver.enqueue(p, from)
    #[inline]
    fn enqueue(&mut self, p: u32, from: u32) -> bool {
        if self.is_satisfied(p) {
            return true;
        }
        if self.is_falsified(p) {
            return false;
        }
        self.falsified[(p ^ 1) as usize] = true;
        let v = (p >> 1) as usize;
        self.level[v] = self.decision_level() as i32;
        self.reason[v] = from;
        self.trail.push(p);
        true
    }

    // Java: Solver.undoOne
    fn undo_one(&mut self) {
        let p = self.trail.pop().unwrap();
        let x = (p >> 1) as usize;
        self.falsified[p as usize] = false;
        self.falsified[(p ^ 1) as usize] = false;
        self.reason[x] = NONE;
        self.level[x] = -1;
        // VarOrderHeap.undo
        if !self.heap.in_heap(x as u32) {
            self.heap.insert(&self.activity, x as u32);
        }
    }

    fn cancel(&mut self) {
        let lim = *self.trail_lim.last().unwrap();
        let mut c = self.trail.len() as isize - lim as isize;
        while c > 0 {
            self.undo_one();
            c -= 1;
        }
        self.trail_lim.pop();
    }

    fn cancel_until(&mut self, level: usize) {
        while self.decision_level() > level {
            self.cancel();
        }
        self.qhead = self.trail.len();
    }

    // ------------------------------------------------------------------ propagation

    // Java: Constr.propagate(s, p) for the three clause kinds; false = conflict
    fn propagate_constr(&mut self, id: u32, p: u32) -> bool {
        let kind = self.arena[id as usize].kind;
        match kind {
            Kind::Bin => {
                self.watches[p as usize].push(id);
                let (head, tail) = {
                    let c = &self.arena[id as usize];
                    (c.lits[0], c.lits[1])
                };
                if head == (p ^ 1) {
                    self.enqueue(tail, id)
                } else {
                    self.enqueue(head, id)
                }
            }
            Kind::Wl => {
                let np = p ^ 1;
                let n = self.arena[id as usize].lits.len();
                {
                    let lits = &mut self.arena[id as usize].lits;
                    if lits[0] == np {
                        lits[0] = lits[1];
                        lits[1] = np;
                    }
                }
                let mut previous = np;
                for i in 2..n {
                    let li = self.arena[id as usize].lits[i];
                    if !self.falsified[li as usize] {
                        let lits = &mut self.arena[id as usize].lits;
                        lits[1] = li;
                        lits[i] = previous;
                        self.watches[(li ^ 1) as usize].push(id);
                        return true;
                    } else {
                        let lits = &mut self.arena[id as usize].lits;
                        let tmp = previous;
                        previous = lits[i];
                        lits[i] = tmp;
                    }
                }
                let first = {
                    let lits = &mut self.arena[id as usize].lits;
                    for i in 2..n {
                        lits[i - 1] = lits[i];
                    }
                    lits[n - 1] = previous;
                    lits[0]
                };
                self.watches[p as usize].push(id);
                self.enqueue(first, id)
            }
            Kind::Unit => unreachable!("unit clauses are never watched"),
        }
    }

    // Java: Solver.propagate
    fn propagate(&mut self) -> u32 {
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            let mut lw = std::mem::take(&mut self.watched);
            lw.clear();
            lw.extend(self.watches[p as usize].drain(..));
            let size = lw.len();
            for i in 0..size {
                let c = lw[i];
                if !self.propagate_constr(c, p) {
                    for &rest in &lw[i + 1..size] {
                        self.watches[p as usize].push(rest);
                    }
                    self.qhead = self.trail.len();
                    self.watched = lw;
                    return c;
                }
            }
            self.watched = lw;
        }
        NONE
    }

    // ------------------------------------------------------------------ activities

    // Java: VarOrderHeap.updateVar
    #[inline]
    fn update_var(&mut self, p: u32) {
        let var = (p >> 1) as usize;
        self.activity[var] += self.var_inc;
        if self.activity[var] > VAR_RESCALE_BOUND {
            for a in self.activity.iter_mut().skip(1) {
                *a *= VAR_RESCALE_FACTOR;
            }
            self.var_inc *= VAR_RESCALE_FACTOR;
        }
        if self.heap.in_heap(var as u32) {
            let i = self.heap.indices[var] as usize;
            self.heap.percolate_up(&self.activity, i);
        }
    }

    // Java: VarOrderHeap.init (+ RSATPhaseSelectionStrategy.init)
    fn order_init(&mut self) {
        let nlength = self.maxvarid + 1;
        if self.activity.len() < nlength {
            self.activity = vec![0.0; nlength];
        }
        if self.phase.len() < nlength {
            self.phase = vec![0; nlength];
        }
        for i in 1..nlength {
            self.phase[i] = ((i as u32) << 1) | 1; // negLit(i)
        }
        self.activity[0] = -1.0;
        self.heap = Heap::new(nlength);
        for i in 1..nlength {
            self.activity[i] = 0.0;
            if i < self.pool.len() && self.pool[i] {
                self.heap.insert(&self.activity, i as u32);
            }
        }
    }

    // Java: VarOrderHeap.select
    fn select(&mut self) -> u32 {
        while !self.heap.empty() {
            let var = self.heap.getmin(&self.activity);
            let next = self.phase[var as usize];
            if self.is_unassigned(next) {
                return next;
            }
        }
        UNDEFINED
    }

    // ------------------------------------------------------------------ conflict analysis

    // Java: Constr.calcReason(p, outReason)
    fn calc_reason(&mut self, id: u32, p: u32) {
        let c = &self.arena[id as usize];
        match c.kind {
            Kind::Unit => {
                if p == UNDEFINED {
                    // Java pushes LiteralsUtils.neg(ILits.UNDEFINED) here; never reached for Kodkod problems
                    self.preason.push(UNDEFINED);
                }
            }
            Kind::Bin => {
                let (h, t) = (c.lits[0], c.lits[1]);
                if self.falsified[h as usize] {
                    self.preason.push(h ^ 1);
                }
                if self.falsified[t as usize] {
                    self.preason.push(t ^ 1);
                }
            }
            Kind::Wl => {
                let start = if p == UNDEFINED { 0 } else { 1 };
                for i in start..c.lits.len() {
                    self.preason.push(c.lits[i] ^ 1);
                }
            }
        }
    }

    #[inline]
    fn set_seen(&mut self, v: usize) {
        if !self.seen[v] {
            self.seen[v] = true;
            self.seen_dirty.push(v as u32);
        }
    }

    // Java: Solver.analyze; returns (learnt clause id, backtrack level)
    fn analyze(&mut self, mut confl: u32) -> (u32, usize) {
        for &v in &self.seen_dirty {
            self.seen[v as usize] = false;
        }
        self.seen_dirty.clear();
        self.out_learnt.clear();
        let mut counter: i32 = 0;
        let mut p = UNDEFINED;
        self.out_learnt.push(UNDEFINED);
        let mut out_btlevel: i32 = 0;
        let mut prev_confl = NONE;
        let dl = self.decision_level() as i32;
        loop {
            self.preason.clear();
            if prev_confl != confl {
                self.calc_reason(confl, p);
                for j in 0..self.preason.len() {
                    let q = self.preason[j];
                    self.update_var(q);
                    let v = (q >> 1) as usize;
                    if !self.seen[v] {
                        self.set_seen(v);
                        let lq = self.get_level(q);
                        if lq == dl {
                            counter += 1;
                        } else if lq > 0 {
                            self.out_learnt.push(q ^ 1);
                            out_btlevel = out_btlevel.max(lq);
                        }
                    }
                }
            }
            prev_confl = confl;
            loop {
                p = *self.trail.last().unwrap();
                confl = self.get_reason(p);
                self.undo_one();
                if self.seen[(p >> 1) as usize] {
                    break;
                }
            }
            counter -= 1;
            if counter <= 0 {
                break;
            }
        }
        self.out_learnt[0] = p ^ 1;
        self.expensive_simplification();
        // Java: dsfactory.createUnregisteredClause(outLearnt)
        let lits = std::mem::take(&mut self.out_learnt);
        let kind = match lits.len() {
            1 => Kind::Unit,
            2 => Kind::Bin,
            _ => Kind::Wl,
        };
        let id = self.new_constr(kind, true, lits);
        self.glucose_on_conflict(id);
        (id, out_btlevel as usize)
    }

    // Java: Solver.expensiveSimplification
    fn expensive_simplification(&mut self) {
        self.analyzetoclear.clear();
        self.analyzetoclear.extend_from_slice(&self.out_learnt);
        let n = self.out_learnt.len();
        let mut j = 1;
        for i in 1..n {
            let l = self.out_learnt[i];
            if self.get_reason(l) == NONE || !self.analyze_removable(l) {
                self.out_learnt[j] = self.out_learnt[i];
                j += 1;
            }
        }
        self.out_learnt.truncate(j);
    }

    // Java: Solver.analyzeRemovable
    fn analyze_removable(&mut self, p: u32) -> bool {
        self.analyzestack.clear();
        self.analyzestack.push(p);
        let top = self.analyzetoclear.len();
        while let Some(q) = self.analyzestack.pop() {
            let c = self.get_reason(q);
            let n = self.arena[c as usize].lits.len();
            for i in 0..n {
                let l = self.arena[c as usize].lits[i];
                let v = (l >> 1) as usize;
                if !self.seen[v] && self.falsified[l as usize] && self.level[v] != 0 {
                    if self.reason[v] == NONE {
                        for k in top..self.analyzetoclear.len() {
                            let w = (self.analyzetoclear[k] >> 1) as usize;
                            self.seen[w] = false;
                        }
                        self.analyzetoclear.truncate(top);
                        return false;
                    }
                    self.set_seen(v);
                    self.analyzestack.push(l);
                    self.analyzetoclear.push(l);
                }
            }
        }
        true
    }

    // Java: glucose.onConflict
    fn glucose_on_conflict(&mut self, id: u32) {
        let mut nblevel = 1;
        self.flag += 1;
        let n = self.arena[id as usize].lits.len();
        for i in 1..n {
            let lvl = self.get_level(self.arena[id as usize].lits[i]) as usize;
            if self.flags[lvl] != self.flag {
                self.flags[lvl] = self.flag;
                nblevel += 1;
            }
        }
        let c = &mut self.arena[id as usize];
        if c.kind != Kind::Unit {
            c.activity += nblevel as f64; // Learnt*.incActivity
        }
    }

    // Java: Solver.record
    fn record(&mut self, id: u32) {
        let (kind, first) = {
            let c = &self.arena[id as usize];
            (c.kind, c.lits[0])
        };
        // assertConstraint
        self.enqueue(first, id);
        if kind == Kind::Unit {
            return;
        }
        // MiniSATLearning.learns: claBumpActivity (variable bumps) then Solver.learn
        let n = self.arena[id as usize].lits.len();
        for i in 0..n {
            let q = self.arena[id as usize].lits[i];
            self.update_var(q);
        }
        self.learnts.push(id);
        // register()
        if kind == Kind::Wl {
            // LearntWLClause.register: the highest-level literal among lits[1..] moves to position 1
            let mut maxi = 1;
            let mut maxlevel = self.get_level(self.arena[id as usize].lits[1]);
            for i in 2..n {
                let level = self.get_level(self.arena[id as usize].lits[i]);
                if level > maxlevel {
                    maxi = i;
                    maxlevel = level;
                }
            }
            self.arena[id as usize].lits.swap(1, maxi);
        }
        let (w0, w1) = {
            let c = &self.arena[id as usize];
            (c.lits[0] ^ 1, c.lits[1] ^ 1)
        };
        self.watches[w0 as usize].push(id);
        self.watches[w1 as usize].push(id);
    }

    // ------------------------------------------------------------------ clause database

    fn locked(&self, id: u32) -> bool {
        let c = &self.arena[id as usize];
        match c.kind {
            Kind::Bin => self.get_reason(c.lits[0]) == id || self.get_reason(c.lits[1]) == id,
            Kind::Wl => self.get_reason(c.lits[0]) == id,
            Kind::Unit => false,
        }
    }

    // Java: Constr.remove -> voc.watches(..).remove(this) (identity, shifting)
    fn remove_constr(&mut self, id: u32) {
        let (w0, w1) = {
            let c = &self.arena[id as usize];
            (c.lits[0] ^ 1, c.lits[1] ^ 1)
        };
        for w in [w0, w1] {
            let list = &mut self.watches[w as usize];
            if let Some(pos) = list.iter().position(|&x| x == id) {
                list.remove(pos);
            }
        }
    }

    // Java: ActivityComparator.compare
    fn cmp_activity(&self, a: u32, b: u32) -> i32 {
        let (ca, cb) = (&self.arena[a as usize], &self.arena[b as usize]);
        let delta = java_round(ca.activity - cb.activity);
        if delta == 0 {
            ca.lits.len() as i32 - cb.lits.len() as i32
        } else {
            delta as i32
        }
    }

    // Java: Vec.selectionSort / Vec.sort (SAT4J's quicksort; not stable)
    fn sort_learnts(&mut self, v: &mut [u32], from: usize, to: usize) {
        let width = to - from;
        if width <= 15 {
            if to == 0 {
                return;
            }
            let mut i = from;
            while i + 1 < to {
                let mut best = i;
                for j in i + 1..to {
                    if self.cmp_activity(v[j], v[best]) < 0 {
                        best = j;
                    }
                }
                v.swap(i, best);
                i += 1;
            }
        } else {
            let pivot = v[width / 2 + from];
            let mut i = from as isize - 1;
            let mut j = to as isize;
            loop {
                loop {
                    i += 1;
                    if self.cmp_activity(v[i as usize], pivot) >= 0 {
                        break;
                    }
                }
                loop {
                    j -= 1;
                    if self.cmp_activity(pivot, v[j as usize]) >= 0 {
                        break;
                    }
                }
                if i >= j {
                    break;
                }
                v.swap(i as usize, j as usize);
            }
            self.sort_learnts(v, from, i as usize);
            self.sort_learnts(v, i as usize, to);
        }
    }

    // Java: glucose.reduce (via Solver.reduceDB)
    fn reduce_db(&mut self) {
        let mut l = std::mem::take(&mut self.learnts);
        let n = l.len();
        self.sort_learnts(&mut l, 0, n);
        let mut j = n / 2;
        for i in n / 2..n {
            let c = l[i];
            if self.locked(c) || self.arena[c as usize].activity <= 2.0 {
                l[j] = l[i];
                j += 1;
            } else {
                self.remove_constr(c);
            }
        }
        l.truncate(j);
        self.learnts = l;
    }

    // glucose clauseManagement ConflictTimerAdapter(1000).newConflict
    fn new_conflict(&mut self) {
        self.cm_counter += 1;
        if self.cm_counter == 1000 {
            self.nbconflict += 1000;
            if self.nbconflict >= self.nextbound {
                self.nextbound += 1000;
                if self.nextbound > self.wall {
                    self.nextbound = self.wall;
                }
                self.nbconflict = 0;
                self.need_to_reduce_db = true;
            }
            self.cm_counter = 0;
        }
    }

    // ------------------------------------------------------------------ search

    fn stopped(&self) -> bool {
        self.stop.as_ref().is_some_and(|f| f.load(Ordering::Relaxed))
    }

    // Java: Solver.modelFound
    fn model_found(&mut self) {
        let n = self.maxvarid; // realNumberOfVariables()
        self.user_model = vec![false; n];
        let nv = if self.declared_max_var_id == 0 { self.maxvarid } else { self.declared_max_var_id };
        for i in 1..=n.max(nv) {
            if i <= n && i < self.pool.len() && self.pool[i] {
                let p = (i as u32) << 1;
                if !self.is_unassigned(p) {
                    self.user_model[i - 1] = self.is_satisfied(p);
                }
            }
        }
        self.cancel_until(self.root_level);
    }

    // Java: Solver.search
    fn search(&mut self, nof_conflicts: i64) -> Lbool {
        let mut conflict_c: i64 = 0;
        self.var_decay = 1.0 / VAR_DECAY;
        self.cla_decay = 1.0 / CLA_DECAY;
        loop {
            let confl = self.propagate();
            if confl == NONE {
                if self.trail.len() == self.realn_vars {
                    self.model_found();
                    return Lbool::True;
                }
                if conflict_c >= nof_conflicts {
                    self.cancel_until(self.root_level);
                    return Lbool::Undefined;
                }
                if self.need_to_reduce_db {
                    self.reduce_db();
                    self.need_to_reduce_db = false;
                }
                let p = self.select();
                // assume(p)
                self.trail_lim.push(self.trail.len());
                self.enqueue(p, NONE);
            } else {
                conflict_c += 1;
                self.new_conflict();
                if self.decision_level() == self.root_level {
                    return Lbool::False;
                }
                let (learnt, bt) = self.analyze(confl);
                let backjump = bt.max(self.root_level);
                self.cancel_until(backjump);
                if backjump == self.root_level {
                    conflict_c = 0;
                }
                self.record(learnt);
                // decayActivities
                self.var_inc *= self.var_decay;
                self.cla_inc *= self.cla_decay;
            }
            if self.stopped() {
                return Lbool::Undefined;
            }
        }
    }

    // Java: Solver.isSatisfiable(VecInt.EMPTY, false); None = aborted
    fn is_satisfiable(&mut self) -> Option<bool> {
        let howmany = self.maxvarid;
        if self.seen.len() <= howmany {
            self.seen = vec![false; howmany + 1];
            self.seen_dirty.clear();
        }
        self.user_model.clear();
        self.order_init();
        // glucose.init
        self.wall = (self.constrs.len() as i32).max(10000);
        if self.flags.len() <= howmany {
            self.flags = vec![0; howmany + 1];
        }
        self.flag = 0;
        self.cm_counter = 0;
        self.nextbound = 5000;
        if self.nbconflict >= self.nextbound {
            self.nbconflict = 0;
            self.need_to_reduce_db = true;
        }
        self.qhead = 0;
        let confl = self.propagate();
        if confl != NONE {
            self.cancel_until(0);
            return Some(false);
        }
        self.root_level = self.decision_level();
        self.order_init(); // duplicated on purpose (Java)
        // ArminRestarts.init
        self.inner = INIT_CONFLICT_BOUND;
        self.outer = INIT_CONFLICT_BOUND;
        self.restart_conflicts = java_round(self.inner);
        self.need_to_reduce_db = false;
        let mut status = Lbool::Undefined;
        while status == Lbool::Undefined {
            status = self.search(self.restart_conflicts);
            if status == Lbool::Undefined {
                if self.stopped() {
                    self.cancel_until(0);
                    return None;
                }
                // ArminRestarts.onRestart
                if self.inner >= self.outer {
                    self.outer *= CONFLICT_BOUND_INC;
                    self.inner = INIT_CONFLICT_BOUND;
                } else {
                    self.inner *= CONFLICT_BOUND_INC;
                }
                self.restart_conflicts = java_round(self.inner);
            }
        }
        self.cancel_until(0);
        Some(status == Lbool::True)
    }
}

impl crate::SatSolver for Sat4j {
    fn num_vars(&self) -> u32 {
        self.vars
    }
    fn num_clauses(&self) -> u64 {
        self.clauses
    }
    fn add_variables(&mut self, n: u32) {
        Sat4j::add_variables(self, n)
    }
    fn add_clause(&mut self, lits: &[i32]) -> bool {
        Sat4j::add_clause(self, lits)
    }
    fn solve(&mut self) -> Option<bool> {
        Sat4j::solve(self)
    }
    fn set_stop_flag(&mut self, flag: Arc<AtomicBool>) {
        Sat4j::set_stop_flag(self, flag)
    }
    fn value_of(&self, v: u32) -> bool {
        Sat4j::value_of(self, v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn java_round_matches_java() {
        assert_eq!(java_round(2.5), 3);
        assert_eq!(java_round(-2.5), -2);
        assert_eq!(java_round(-0.5), 0);
        assert_eq!(java_round(110.00000000000001), 110);
        assert_eq!(java_round(-3.0), -3);
    }

    #[test]
    fn small_sat_and_unsat() {
        let mut s = Sat4j::new();
        s.add_variables(3);
        assert!(s.add_clause(&[1, 2]));
        assert!(s.add_clause(&[-1, 3]));
        assert!(s.add_clause(&[-2, -3]));
        assert_eq!(s.solve(), Some(true));
        let m: Vec<bool> = (1..=3).map(|v| s.value_of(v)).collect();
        assert!((m[0] || m[1]) && (!m[0] || m[2]) && (!m[1] || !m[2]));

        let mut u = Sat4j::new();
        u.add_variables(1);
        u.add_clause(&[1]);
        u.add_clause(&[-1]);
        assert_eq!(u.solve(), Some(false));
    }
}
