//! Port of `kodkod.engine.fol2sat.Bool2CNFTranslator` (+ `PolarityDetector`): Plaisted-Greenbaum CNF with gate
//! labels as CNF variables.

use crate::bool::*;
use std::collections::HashSet;

/// Receiver of the clause stream (`SATSolver.addVariables` / `addClause`).
pub trait CnfSink {
    fn num_vars(&self) -> i32;
    fn add_variables(&mut self, n: i32);
    fn add_clause(&mut self, lits: &[i32]);
}

impl CnfSink for satsolver::sat4j::Sat4j {
    fn num_vars(&self) -> i32 {
        satsolver::sat4j::Sat4j::num_vars(self) as i32
    }
    fn add_variables(&mut self, n: i32) {
        satsolver::sat4j::Sat4j::add_variables(self, n as u32)
    }
    fn add_clause(&mut self, lits: &[i32]) {
        satsolver::sat4j::Sat4j::add_clause(self, lits);
    }
}

/// `Bool2CNFTranslator.translate(BooleanConstant)`
pub fn translate_constant(value: BV, sink: &mut dyn CnfSink) {
    if value == FALSE {
        sink.add_clause(&[]);
    }
}

struct Pol {
    offset: i32,
    pol: Vec<u8>,
}

impl Pol {
    fn visited(&mut self, label: i32, p: u8) -> bool {
        let i = (label - self.offset) as usize;
        let v = self.pol[i];
        self.pol[i] = v | p;
        (v | p) == v
    }
    fn visit(&mut self, f: &Factory, v: BV, arg: u8) {
        if v < 0 {
            // NotGate: ints[3-arg] with ints = {3, 1, 2}
            let na = match arg {
                1 => 2,
                2 => 1,
                _ => 3,
            };
            return self.visit(f, -v, na);
        }
        match f.op(v) {
            Op::Var | Op::Const => {}
            Op::And | Op::Or => {
                if !self.visited(v, arg) {
                    for &i in f.inputs(v) {
                        self.visit(f, i, arg);
                    }
                }
            }
            Op::Ite => {
                if !self.visited(v, arg) {
                    let ins = f.inputs(v).to_vec();
                    self.visit(f, ins[0], 3);
                    self.visit(f, ins[1], arg);
                    self.visit(f, ins[2], arg);
                }
            }
            Op::Not => unreachable!(),
        }
    }
    fn positive(&self, label: i32) -> bool {
        self.pol[(label - self.offset) as usize] & 1 > 0
    }
    fn negative(&self, label: i32) -> bool {
        self.pol[(label - self.offset) as usize] & 2 > 0
    }
}

struct Tr<'a> {
    f: &'a Factory,
    pol: Pol,
    visited: HashSet<i32>,
    sink: &'a mut dyn CnfSink,
    buf: Vec<i32>,
}

impl Tr<'_> {
    fn visit(&mut self, v: BV) -> i32 {
        if v < 0 {
            return -self.visit(-v);
        }
        match self.f.op(v) {
            Op::Var => v,
            Op::And | Op::Or => {
                if self.visited.insert(v) {
                    let and = self.f.op(v) == Op::And;
                    let (sgn, p, n) = if and {
                        (1, self.pol.positive(v), self.pol.negative(v))
                    } else {
                        (-1, self.pol.negative(v), self.pol.positive(v))
                    };
                    let output = v * -sgn;
                    let mut last: Vec<i32> = if n { Vec::with_capacity(self.f.inputs(v).len() + 1) } else { Vec::new() };
                    let ins = self.f.inputs(v).to_vec();
                    for i in ins {
                        let il = self.visit(i);
                        if p {
                            self.sink.add_clause(&[il * sgn, output]);
                        }
                        if n {
                            last.push(il * -sgn);
                        }
                    }
                    if n {
                        last.push(v * sgn);
                        self.sink.add_clause(&last);
                    }
                }
                v
            }
            Op::Ite => {
                if self.visited.insert(v) {
                    let ins = self.f.inputs(v).to_vec();
                    let i = self.visit(ins[0]);
                    let t = self.visit(ins[1]);
                    let e = self.visit(ins[2]);
                    let (p, n) = (self.pol.positive(v), self.pol.negative(v));
                    if p {
                        self.sink.add_clause(&[-i, t, -v]);
                        self.sink.add_clause(&[i, e, -v]);
                        self.sink.add_clause(&[t, e, -v]);
                    }
                    if n {
                        self.sink.add_clause(&[-i, -t, v]);
                        self.sink.add_clause(&[i, -e, v]);
                        self.sink.add_clause(&[-t, -e, v]);
                    }
                }
                v
            }
            Op::Const | Op::Not => unreachable!(),
        }
    }
}

/// `Bool2CNFTranslator.translate(circuit, maxPrimaryVar, factory)` for a non-constant circuit.
pub fn translate(f: &Factory, circuit: BV, max_primary_var: i32, sink: &mut dyn CnfSink) {
    let max_literal = circuit.abs();
    let mut pol = Pol { offset: max_primary_var + 1, pol: vec![0u8; (max_literal - max_primary_var).max(0) as usize] };
    pol.visit(f, circuit, 1);
    let new_vars = max_literal.max(max_primary_var) - sink.num_vars();
    if new_vars > 0 {
        sink.add_variables(new_vars);
    }
    let mut tr = Tr { f, pol, visited: HashSet::new(), sink, buf: Vec::new() };
    let _ = &tr.buf;
    if circuit > 0 && f.op(circuit) == Op::And {
        let ins = f.inputs(circuit).to_vec();
        for &i in &ins {
            tr.visit(i);
        }
        for &i in &ins {
            tr.sink.add_clause(&[i]);
        }
    } else {
        let l = tr.visit(circuit);
        tr.sink.add_clause(&[l]);
    }
}
