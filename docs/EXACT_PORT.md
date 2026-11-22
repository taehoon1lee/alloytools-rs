# Exact (Java-identical) instance pipeline

Goal: `alloy-rs` prints the **same first instance / counterexample** as Java Alloy 6.2.0 for every SAT command
(not just the same SAT/UNSAT). Java's first model is an artifact of the CNF *and* SAT4J's search, so the exact path
must reproduce, bit for bit: Alloy→Kodkod translation → Pardinus/Kodkod `Translator` (symbolic-bound resolution,
predicate inlining + total-order breaking, skolemization, FOL→boolean circuit with CBC hash-consing, lex-leader SBP,
Plaisted-Greenbaum CNF) → SAT4J 2.3.1 default solver → `A4Solution` atom renaming + sig/field/skolem evaluation.

The existing fast pipeline (crates/kodkod, portfolio SAT) stays for verdicts/perf; the exact pipeline is used to
produce the instance. `alloy_translate::execute_command` starts `exact::solve_first` on its own thread next to the
fast pipeline: an UNSAT from the fast side stops it (SAT4J, the FOL→boolean translation and the trace-length loop
honour the stop flag); a SAT result waits for the exact instance and falls back to the fast instance if the exact
side fails. `ALLOY_RS_NO_EXACT=1` disables it.

**Status (2026-11-22): done.** All 215 SAT commands of the corpus with a golden instance (static and temporal) give
the identical first instance through the CLI (`python harness/check.py --verbose`: 215 identical, 0 differ).

## Stages and their ground truth (all verified against Java dumps, never read by Rust code)
| stage | Rust | verified by | status |
|---|---|---|---|
| SAT4J 2.3.1 `newDefault()` | `crates/satsolver/src/sat4j.rs` | replay `out/*.cnf` (`cargo run --release -p satsolver --example sat4j_replay -- tools/exact/out/*.cnf`) | **216/216 models identical** |
| Kodkod `Translator` (Kodkod problem → CNF) | `crates/pardinus` | `cargo run --release -p pardinus --example kk_cnf -- tools/exact/out/*.kk` | **207/207 static problems: identical CNF call sequence** |
| Alloy → Kodkod (`TranslateAlloyToKodkod`, `BoundsComputer`, `ScopeComputer`, `Simplifier`, A4Solution setup) | `crates/alloy-translate/src/exact/` | `python tools/exact/cmp_alloy.py` (`.kk` text + CNF of every SAT call) | **215/215 CNF identical**, 213/215 `.kk` text (spanning: Java shares one bound node across `r, t1, t2: univ->univ`; no CNF effect) |
| `A4Solution.rename` + eval → instance JSON | `exact/instance.rs` | `python tools/exact/cmp_inst.py` (vs harness goldens) | **215/215 identical** |
| Pardinus temporal (`TemporalPardinusSolver`, LTL2FOL, bounds expansion, `TemporalInstance`) | `crates/pardinus/src/temporal.rs` | `cmp_alloy.py` (one CNF block per trace length) | **8/8 identical** |

## Tools (`tools/exact/`)
- `python tools/exact/build.py` — compiles `java/edu/mit/csail/sdg/translator/*.java` against the Alloy jar.
- `python tools/exact/trace_all.py [check|all] [-j N] [--filter S]` — writes `out/<tag>.{kk,cnf,json}` (tag =
  corpus id with `/`→`__` + `#<cmd>`), checks json == golden instance and Java replay of the cnf.
- `KKDump.java` — hooks `PardinusSolver.solveAll` (subclass installed into `A4Solution.solver` by reflection), dumps
  formula DAG + `PardinusBounds` (concrete + symbolic bounds, int bounds, relation order) + options.
- `TraceOracle.java` — SAT4J wrapper recording every `addVariables`/`addClause` + model; `replay` mode.
- `PinCheck.java` — validates an arbitrary (Rust) instance by pinning it into Java's bounds and re-solving.
- `cmp_alloy.py` + `crates/alloy-translate/examples/exact_cmp.rs` — Rust `.kk` text / CNF vs `out/` (temporal: per
  trace length; `DUMP_TCNF=1` writes `<tag>.rust.cnf`, a differing `.kk` is written to `<tag>.rust.kk`).
- `cmp_inst.py` + `examples/exact_inst.rs` — Rust first instance (all states) vs the harness golden instances.
- Java lex-leader chains: run the oracle with `-Ddebug=yes -Dorg.slf4j.simpleLogger.defaultLogLevel=debug`
  (`lex: [...]` lines, truncated to 320 chars).
- `jstrip.py` — comment stripper for reading big Java files (the naive sed range strip loses code!).
- SAT4J 2.3.1 sources: `https://repo1.maven.org/maven2/org/sat4j/org.sat4j.core/2.3.1/` (sources jar; the jar's
  `Solver.class` is byte-identical to the one inside the Alloy dist jar).

## .kk format (KKDump)
`U n` + `A "atom"`×n; `O key=value…`; nodes `n <id> KIND args` emitted before use (REL arity var atom "name",
VAR arity "name", CONSTE/CONSTF, BINE op l r, UNE op e, NARYE op c…, COMPR decls f, IFE c t e, PROJ e cols…,
I2E op i, E2I op e, ICONST v, BINI/NARYI/UNI, SUM decls i, IFI, ICMP op l r, CMP op l r, MULT mult e,
QUANT q decls f, BINF op l r, NARYF op c…, NOT f, PACYCLIC r, PFUNCTION r dom mult rng, PTOTAL r ord first last,
DECL var mult expr, DECLS d…, UTEMPF/BTEMPF/TEMPE); then `R relid` (bounds.relations() order), `L/H relid idx…`
(concrete lower/upper, absent when symbolic-only), `SB relid lo hi` (symbolic, insertion order), `IB int idx…`,
`G goal`. Node ids preserve Java object identity (sharing).

## Exactness notes (things that bit or will bite)
- SAT4J: phase is always the negative literal (VarOrderHeap.assignLiteral is a no-op, so RSAT never records);
  heap ties never move; learnt activity = LBD (glucose), reduceDB every 5000 then +1000 conflicts (cap
  max(#constrs,10000)), sorted with SAT4J's own quicksort; analyze undoes the trail itself; backjump level is the
  pre-minimization max level; `Vec.remove` shifts, `VecInt.delete` swaps with last.
- Kodkod CBC: gate labels are CNF variables (gaps from unused gates matter, e.g. DefCond overflow gates are always
  built); `CacheSet` inserts at chain head and `resize` reverses chains; lookup returns the first flatten-equivalent
  gate; `superFastHash` with Java int wrap-around.
- FOL2BoolCache caches shared nodes *and* nodes not depending on the innermost quantified variable; which nodes get
  a record depends on traversal order.
- Pardinus symbolic bounds (`Version.experimental=true` in Alloy): `this/Sig.field` often has only a symbolic bound;
  `Translator` resolves them (`PardinusBounds.resolve`) and conjoins extra constraints.

- Alloy-side Java quirks that each cost an exact match (all ported):
  `ExprChoice` resolves top-down (an overloaded right operand of a join is distributed, `CompModule.process`;
  2+ legal all-empty candidates → `none`; the chosen candidate is resolved further); macro arguments are substituted
  as expressions (re-translated at every use, fresh Kodkod nodes); a small-int `fun` body gets an implicit `Int[..]`
  (`resolve_as_set`); `Int[e]` is `e`; `S <: S.f` is `f`; string atoms come in `java.util.HashSet` order of
  `Command.getAllStringConstants`; `Simplifier` tightens bounds before `r = r`; `enum E` opens
  `util/ordering[this/E]` with alias `open$N` (renamed by `doneParsing`), and BoundsComputer pre-binds its
  First/Next; merged module instantiations keep the path minimal by (`$`, `Util.slashComparator`); skolems are shown
  only for variables with an Alloy type (`kv2typepos`).
- Temporal: symbolic-bound constraints over variable relations are wrapped in `always` (PardinusBounds.resolve); the
  lex-leader SBP takes the static entries first, then the entries of each time step (`[HASLab]` loop over
  `lowerBound(STATE)`); LTL2FOL builds fresh nodes per occurrence except for unchanged subtrees.

## Alloy → Kodkod — facts gathered from the Java sources
Target: build a `pardinus::instance::Problem` from the Rust sema `Model` + `RCommand` whose `.kk` serialization is
textually identical to KKDump's (write a `write_kk` in pardinus that emits nodes in KKDump's DFS order: BINE left
then right, NARY children in order, COMPR/QUANT/SUM decls then body, DECL var then expr, then `R`/`L`/`H`/`SB`/`SC`/
`IB`/`G`). Java: `TranslateAlloyToKodkod`, `BoundsComputer`, `ScopeComputer`, `A4Solution` (ctor, addRel/addSig/
addField/query/addFormula/solve), `Simplifier`.
- A4Solution ctor: universe = ScopeComputer atoms; int atoms bound with `bounds.boundExactly(i, {"i"})` for
  min..max, relations created in this order: `Int/min`, `Int/zero`, `Int/max`, `Int/next` (exact), `seq/Int` (0..
  maxseq-1), one unary relation named `""` per string literal (s2k), `String` (exact). Then BoundsComputer.
- BoundsComputer: computeLowerBound/UpperBound over top-level PrimSigs; allocatePrimSig (children first; `no (a&b)`
  disjointness formulas for siblings; `S_remainder` relation for non-abstract sigs with children); subset sigs; the
  `one sig` with 2 fields + totalorder fact special case; fields (`sim()` for `one sig` exactly-of fields; upper =
  union over `f.type().fold()` of products of sig uppers; `one sig` fields are `a2k(S).product(r)` with r of arity-1);
  symbolic bounds (addSymbolicBound for non-top-level non-PrimSig... see A4Solution.addSymbolicBound); then per sig
  size/one/some/lone formulas (`size()` uses fresh `v<cnt>` variables).
- Variable names: `TranslateAlloyToKodkod.cnt` is a JVM-global counter (`"v"+cnt++`) used by BoundsComputer.size,
  isInBinary, TOTALORDER fallback. KKDump runs one command per JVM (cnt starts at 0); goldens ran all commands of a
  file in one JVM (cnt carried over) yet all 215 instances matched, so start at 0 unless a diff says otherwise.
  Quantifier variables are `skolem(label)` = `<cmdlabel>_<name>` outside functions (`<func tail>_<name>` inside a
  call; plain name when the label/func name contains `$`).
- makeFacts order: BoundsComputer formulas, then for each reachable sig: per field decl `all this: S | this.f in
  decl.expr` (ExprLet for `one` sigs) [+ `f.univ..univ in S` unless one sig], disj2 / disjoint field constraints,
  then sig facts; then the command formula split on top-level ExprList AND (after ConvToConjunction); A4Solution.solve
  appends `r = r` for every relation in bounds.relations() and builds `Formula.and(formulas)` (NaryFormula).
- ExprList AND/OR → `getSingleFormula` heap-shaped binary tree (me & child 2i & child 2i+1), NOT a flat Nary.
- ExprCall inlines the body with an env of `cset(args)`; 0-arity functions are cached per Func (cacheForConstants).
- isIn/isInBinary: arrow multiplicities expand to quantified formulas with fresh `v<cnt>` variables (am=true).
- ExprQt: desugar (disj), addOne (unary decl without multiplicity → ONEOF), one/lone → comprehension.one/lone when
  all decls are unary ONEOF, else LONE = all/all pairs; guards for non-unary decls.
