//! Port of `kodkod/instance` (Universe, Tuple, TupleSet, Bounds, Instance).
//!
//! Atoms are `u32` indices into the [`Universe`]; a tuple is a `Vec<u32>` of atom indices. A
//! [`TupleSet`] is a sorted set of same-arity tuples, which is what Kodkod's bounds are made of.

use std::collections::{BTreeMap, BTreeSet};

use crate::ast::RelId;

/// Ordered set of atoms (Java `kodkod.instance.Universe`).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Universe {
    atoms: Vec<String>,
}

impl Universe {
    pub fn new(atoms: Vec<String>) -> Result<Self, String> {
        let mut seen = BTreeSet::new();
        for a in &atoms {
            if !seen.insert(a.clone()) {
                return Err(format!("duplicate atom {a}"));
            }
        }
        Ok(Universe { atoms })
    }
    pub fn size(&self) -> usize {
        self.atoms.len()
    }
    pub fn atom(&self, i: u32) -> &str {
        &self.atoms[i as usize]
    }
    pub fn atoms(&self) -> &[String] {
        &self.atoms
    }
    pub fn index_of(&self, name: &str) -> Option<u32> {
        self.atoms.iter().position(|a| a == name).map(|i| i as u32)
    }
}

/// Java `kodkod.instance.TupleSet`: tuples of one arity over a universe.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct TupleSet {
    pub arity: usize,
    pub tuples: BTreeSet<Vec<u32>>,
}

impl TupleSet {
    pub fn empty(arity: usize) -> Self {
        TupleSet {
            arity,
            tuples: BTreeSet::new(),
        }
    }

    pub fn from_tuples(arity: usize, tuples: impl IntoIterator<Item = Vec<u32>>) -> Self {
        let mut t = TupleSet::empty(arity);
        for x in tuples {
            debug_assert_eq!(x.len(), arity);
            t.tuples.insert(x);
        }
        t
    }

    /// All tuples of `arity` over `n` atoms (Java `TupleFactory.allOf` for a product of atoms).
    pub fn all(arity: usize, n: u32) -> Self {
        let mut out = BTreeSet::new();
        let mut cur = vec![0u32; arity];
        if n > 0 || arity == 0 {
            loop {
                out.insert(cur.clone());
                let mut k = arity;
                loop {
                    if k == 0 {
                        return TupleSet { arity, tuples: out };
                    }
                    k -= 1;
                    cur[k] += 1;
                    if cur[k] < n {
                        break;
                    }
                    cur[k] = 0;
                }
            }
        }
        TupleSet { arity, tuples: out }
    }

    pub fn len(&self) -> usize {
        self.tuples.len()
    }

    pub fn is_empty(&self) -> bool {
        self.tuples.is_empty()
    }

    pub fn contains(&self, t: &[u32]) -> bool {
        self.tuples.contains(t)
    }

    pub fn union(&self, o: &TupleSet) -> TupleSet {
        TupleSet {
            arity: self.arity,
            tuples: self.tuples.union(&o.tuples).cloned().collect(),
        }
    }

    pub fn difference(&self, o: &TupleSet) -> TupleSet {
        TupleSet {
            arity: self.arity,
            tuples: self.tuples.difference(&o.tuples).cloned().collect(),
        }
    }

    pub fn product(&self, o: &TupleSet) -> TupleSet {
        let mut out = BTreeSet::new();
        for a in &self.tuples {
            for b in &o.tuples {
                let mut t = a.clone();
                t.extend_from_slice(b);
                out.insert(t);
            }
        }
        TupleSet {
            arity: self.arity + o.arity,
            tuples: out,
        }
    }
}

/// Bounds of one relation (Java `Bounds.lowerBound/upperBound`).
#[derive(Debug, Clone)]
pub struct RelBound {
    pub name: String,
    pub arity: usize,
    pub lower: TupleSet,
    pub upper: TupleSet,
}

/// Lower/upper bounds for every relation of a problem (Java `kodkod.instance.Bounds`).
#[derive(Debug, Clone)]
pub struct Bounds {
    pub universe: Universe,
    pub relations: Vec<RelBound>,
    /// Bitwidth of the integers (`0` = no integers in the problem).
    pub bitwidth: u32,
    /// Atoms with a fixed meaning (the integers): they never take part in symmetry breaking.
    pub ordered_atoms: std::collections::BTreeSet<u32>,
    /// The integer atoms are `int_start..int_start + 2^bitwidth`; atom `int_start + k` has value `int_min + k`.
    pub int_start: u32,
    pub int_min: i64,
}

impl Bounds {
    pub fn new(universe: Universe) -> Self {
        Bounds {
            universe,
            relations: Vec::new(),
            bitwidth: 0,
            ordered_atoms: BTreeSet::new(),
            int_start: 0,
            int_min: 0,
        }
    }

    /// Declares a relation with `lower ⊆ upper`; returns its id.
    pub fn bound(&mut self, name: &str, lower: TupleSet, upper: TupleSet) -> Result<RelId, String> {
        if lower.arity != upper.arity {
            return Err(format!("arity mismatch for {name}"));
        }
        if !lower.tuples.is_subset(&upper.tuples) {
            return Err(format!("lower bound of {name} is not a subset of its upper bound"));
        }
        self.relations.push(RelBound {
            name: name.to_string(),
            arity: upper.arity,
            lower,
            upper,
        });
        Ok((self.relations.len() - 1) as RelId)
    }

    pub fn rel(&self, id: RelId) -> &RelBound {
        &self.relations[id as usize]
    }
}

/// A satisfying assignment: the tuples of every relation (Java `kodkod.instance.Instance`).
#[derive(Debug, Clone, Default)]
pub struct Instance {
    pub relations: BTreeMap<String, TupleSet>,
    /// Tuples of every relation indexed by its `RelId` in `Bounds::relations`
    /// (preserves distinct relations even when multiple modules share a display label).
    pub by_id: Vec<TupleSet>,
}
