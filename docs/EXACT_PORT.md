# Unified Pardinus Translation & BatSat Verification Pipeline

Goal: `alloy-rs` executes every Alloy command through one pure-Rust, pure-MIT pipeline whose semantics match Java Alloy 6.2.0 bit for bit up to CNF generation (`JavaOrder`), while solving via a fast 4-thread `BatSat` portfolio with runtime model verification:

1. **Alloy → Pardinus (`crates/alloy-translate/src/exact/`)**: `TranslateAlloyToKodkod`, `BoundsComputer`, `ScopeComputer`, `Simplifier`, `Options` (`symmetry`, `skolem_depth`, `no_overflow`, `unrolls`), and `A4Solution` setup.
2. **Pardinus → Circuit & CNF (`crates/pardinus/`)**: symbolic-bound resolution (`PardinusBounds.resolve`), predicate inlining + matrix symmetry breaking, skolemization, FOL → boolean circuit (`Fol2Bool` + flat-pool `CBCFactory` hash-consing), parameterized lex-leader SBP (`JavaOrder`, `ArityDecl`, `DeclOrder`, `NoSbp`), and iterative Plaisted-Greenbaum CNF (`Bool2CNFTranslator`).
3. **Portfolio SAT Solving & Runtime Verification (`pardinus::translator::solve_portfolio`, `pardinus::temporal::solve`)**: builds the base `Fol2Bool` circuit once (`translate_circuit`), branches into 4 `BatSat` worker threads (`JavaOrder`/`NoSbp`/`ArityDecl`/`DeclOrder`, racing restarts + positive/negative polarities with BVE via `satsolver::simp`), and checks every returned SAT model against both the pre-BVE CNF (`cnf::verify_cnf_model`) and the SBP-free circuit (`Factory::eval_bv`). Temporal problems probe `min_trace..=max_trace` via `pardinus::temporal::solve`.
4. **Solution Rendering (`crates/alloy-translate/src/exact/instance.rs`)**: `A4Solution.rename()` (`Sig$i`, `next`/`prev` chain ordering, `unused<i>`, skolems `$name`) and relation/skolem evaluation (`Evaluator`).

Legacy crates/modules (`crates/kodkod/`, `crates/alloy-translate/src/translate.rs`, and the LGPL-2.1/EPL-1.0 `crates/satsolver/src/sat4j.rs` port) have been removed, eliminating dual-pipeline divergence and making the workspace **100% pure MIT**.

**Status (2026-11-24): done.**
- `python harness/check.py --perf`: **199/199** parse/commands, **465/465** verdict, **465/465** perf, **20.47 s** sequential Rust vs **285.66 s** Java (`x0.07`).
- `python harness/check.py --count`: **432/432** solution counts match Java (`symmetry=0`).
- `python tools/exact/cmp_alloy.py`: **215/215** `.kk` text and `JavaOrder` CNF identical (`8/8` temporal).
- `kk_cnf`: **207/207** static `.kk` problems emit identical CNF call sequences.
- `PinCheck.java`: **59/59** static SAT `check` counterexamples verified `RESULT\tSAT` with `OOB=0` and `BADATOM=0`.
- Independent AST verification (`crates/alloy-translate/src/eval/`, `--verify` / `ALLOY_RS_VERIFY=1`): **215/215** Java golden and **215/215** Rust SAT instances verified, **240/240** random LTL+Past differential checks.
- Alloy 6.2.0 XML (`crates/alloy-translate/src/xml.rs`, `--xml <PATH>`): `python tools/xml_check/run_all.py --oracle-self-test` **215/215** (`A4SolutionReader` + `StaticInstanceReader` + `sol.eval()` / pinned SAT4J across 207 static + 8 temporal commands, plus GUI `VizState`).
- `python tools/exact/cmp_inst.py --all -j 6`: **465/465** verdict agreement (`verdict_mismatch=0`, `errors=0`, `missing=0`).

## Stages and their verification (ground truth in `tools/exact/`, never read by Rust code)
| stage | Rust | verified by | status |
|---|---|---|---|
| Kodkod/Pardinus `Translator` (Kodkod problem → CNF) | `crates/pardinus` | `kk_cnf` over static `tools/exact/out/*.kk` | **207/207 static problems: identical CNF call sequence** |
| Alloy → Kodkod/Pardinus (`exact/`) | `crates/alloy-translate/src/exact/` | `python tools/exact/cmp_alloy.py` (`.kk` text + `JavaOrder` CNF) | **215/215 `.kk` text and CNF identical** |
| Pardinus temporal (`TemporalPardinusSolver`, LTL2FOL, bounds expansion, `TemporalInstance`) | `crates/pardinus/src/temporal.rs` | `cmp_alloy.py` (`record=true` mode, one CNF block per trace length) | **8/8 identical** |
| Counterexample cross-check (`A4Solution` instance validation) | `alloy-rs` + `exact/instance.rs` | `PinCheck.java` over all static SAT `check` counterexamples | **59/59 `RESULT\tSAT` (`OOB=0`, `BADATOM=0`)** |
| Full corpus parity & perf | `alloy-translate` + `pardinus` + `satsolver` (`BatSat`) | `check.py --perf`, `check.py --count`, `cmp_inst.py --all` | **465/465 verdict & perf (`20.47s`), 432/432 count** |

## Tools (`tools/exact/`)
- `python tools/exact/build.py` — compiles `java/edu/mit/csail/sdg/translator/*.java` against the Alloy jar.
- `python tools/exact/trace_all.py [check|all] [-j N] [--filter S]` — writes `out/<tag>.{kk,cnf,json}` (tag = corpus id with `/`→`__` + `#<cmd>`), checks json == golden instance and Java replay of the cnf.
- `KKDump.java` — hooks `PardinusSolver.solveAll` (subclass installed into `A4Solution.solver` by reflection), dumps formula DAG + `PardinusBounds` (concrete + symbolic bounds, int bounds, relation order) + options.
- `TraceOracle.java` — SAT4J wrapper recording every `addVariables`/`addClause` + model; `replay` mode.
- `PinCheck.java` — validates a Rust static instance (with `_remainder` derivation and injective atom bijection for renamed sub-sig/ordered atoms) by pinning it into Java's bounds and re-solving.
- `cmp_alloy.py` + `crates/alloy-translate/examples/exact_cmp.rs` — Rust `.kk` text / `JavaOrder` CNF vs `out/` (temporal: per trace length; `DUMP_TCNF=1` writes `<tag>.rust.cnf`, a differing `.kk` is written to `<tag>.rust.kk`).
- `cmp_inst.py` + `examples/exact_inst.rs` — verifies verdict parity across all 465 scored commands and reports identical vs alternative valid SAT instances relative to harness goldens.
- Java lex-leader chains: run the oracle with `-Ddebug=yes -Dorg.slf4j.simpleLogger.defaultLogLevel=debug` (`lex: [...]` lines, truncated to 320 chars).
- `jstrip.py` — comment stripper for reading big Java files (the naive sed range strip loses code!).

## .kk format (KKDump)
`U n` + `A "atom"`×n; `O key=value…`; nodes `n <id> KIND args` emitted before use (REL arity var atom "name", VAR arity "name", CONSTE/CONSTF, BINE op l r, UNE op e, NARYE op c…, COMPR decls f, IFE c t e, PROJ e cols…, I2E op i, E2I op e, ICONST v, BINI/NARYI/UNI, SUM decls i, IFI, ICMP op l r, CMP op l r, MULT mult e, QUANT q decls f, BINF op l r, NARYF op c…, NOT f, PACYCLIC r, PFUNCTION r dom mult rng, PTOTAL r ord first last, DECL var mult expr, DECLS d…, UTEMPF/BTEMPF/TEMPE); then `R relid` (bounds.relations() order), `L/H relid idx…` (concrete lower/upper, absent when symbolic-only), `SB relid lo hi` (symbolic, insertion order), `IB int idx…`, `G goal`. Node ids preserve Java object identity (sharing).

## Exactness notes (things that bit or will bite)
- Kodkod CBC: gate labels are CNF variables (gaps from unused gates matter, e.g. DefCond overflow gates are always built); `CacheSet` inserts at chain head and `resize` reverses chains; lookup returns the first flatten-equivalent gate; `superFastHash` with Java int wrap-around. Note `solve_portfolio` always constructs `SbpOrder::JavaOrder` first on `&mut circ.factory` so gate labels stay deterministic when comparing CNF, while `eval_bv(circ.circuit, ...)` evaluates only `1..=circ.circuit.abs()` (excluding SBP gates).
- FOL2BoolCache caches shared nodes *and* nodes not depending on the innermost quantified variable; which nodes get a record depends on traversal order.
- Pardinus symbolic bounds (`Version.experimental=true` in Alloy): `this/Sig.field` often has only a symbolic bound; `Translator` resolves them (`PardinusBounds.resolve`) and conjoins extra constraints.
- Alloy-side Java quirks that each cost an exact match (all ported):
  `ExprChoice` resolves top-down (an overloaded right operand of a join is distributed, `CompModule.process`; 2+ legal all-empty candidates → `none`; the chosen candidate is resolved further); macro arguments are substituted as expressions (re-translated at every use, fresh Kodkod nodes); a small-int `fun` body gets an implicit `Int[..]` (`resolve_as_set`); `Int[e]` is `e`; `S <: S.f` is `f`; string atoms come in `java.util.HashSet` order of `Command.getAllStringConstants`; `Simplifier` tightens bounds before `r = r`; `enum E` opens `util/ordering[this/E]` with alias `open$N` (renamed by `doneParsing`), and BoundsComputer pre-binds its First/Next; merged module instantiations keep the path minimal by (`$`, `Util.slashComparator`); skolems are shown only for variables with an Alloy type (`kv2typepos`).
- Name lookup is Java's `getRawNQS`/`populate`: names of this module and of every module reachable through opens (private opens only from the module itself), without shadowing; `jtype::check_calls` (port of `CompModule.applicable` on Java's sig-level `Type`) drops overloaded calls whose arguments cannot fit and reports a type error when no candidate is left (`isIntsNotUsed` is `false` in Java, so `integer/` functions always compete). `pred/totalOrder` / `disj` arguments are resolved against each other like `ExprList.resolve`.
- Temporal: symbolic-bound constraints over variable relations are wrapped in `always` (PardinusBounds.resolve); the lex-leader SBP takes the static entries first, then the entries of each time step (`[HASLab]` loop over `lowerBound(STATE)`); LTL2FOL builds fresh nodes per occurrence except for unchanged subtrees.

## Alloy → Kodkod — facts gathered from the Java sources
Build a `pardinus::instance::Problem` from the Rust sema `Model` + `RCommand` whose `.kk` serialization is textually identical to KKDump's (`write_kk` in `pardinus` emits nodes in KKDump's DFS order: BINE left then right, NARY children in order, COMPR/QUANT/SUM decls then body, DECL var then expr, then `R`/`L`/`H`/`SB`/`SC`/`IB`/`G`). Java: `TranslateAlloyToKodkod`, `BoundsComputer`, `ScopeComputer`, `A4Solution` (ctor, addRel/addSig/addField/query/addFormula/solve), `Simplifier`.
- A4Solution ctor: universe = ScopeComputer atoms; int atoms bound with `bounds.boundExactly(i, {"i"})` for min..max, relations created in this order: `Int/min`, `Int/zero`, `Int/max`, `Int/next` (exact), `seq/Int` (0..maxseq-1), one unary relation named `""` per string literal (s2k), `String` (exact). Then BoundsComputer.
- BoundsComputer: computeLowerBound/UpperBound over top-level PrimSigs; allocatePrimSig (children first; `no (a&b)` disjointness formulas for siblings; `S_remainder` relation for non-abstract sigs with children); subset sigs; the `one sig` with 2 fields + totalorder fact special case; fields (`sim()` for `one sig` exactly-of fields; upper = union over `f.type().fold()` of products of sig uppers; `one sig` fields are `a2k(S).product(r)` with r of arity-1); symbolic bounds (addSymbolicBound for non-top-level non-PrimSig... see A4Solution.addSymbolicBound); then per sig size/one/some/lone formulas (`size()` uses fresh `v<cnt>` variables).
- Variable names: `TranslateAlloyToKodkod.cnt` is a JVM-global counter (`"v"+cnt++`) used by BoundsComputer.size, isInBinary, TOTALORDER fallback. KKDump runs one command per JVM (cnt starts at 0); goldens ran all commands of a file in one JVM (cnt carried over) yet all 215 matched, so start at 0 unless a diff says otherwise. Quantifier variables are `skolem(label)` = `<cmdlabel>_<name>` outside functions (`<func tail>_<name>` inside a call; plain name when the label/func name contains `$`).
- makeFacts order: BoundsComputer formulas, then for each reachable sig: per field decl `all this: S | this.f in decl.expr` (ExprLet for `one` sigs) [+ `f.univ..univ in S` unless one sig], disj2 / disjoint field constraints, then sig facts; then the command formula split on top-level ExprList AND (after ConvToConjunction); A4Solution.solve appends `r = r` for every relation in bounds.relations() and builds `Formula.and(formulas)` (NaryFormula).
- ExprList AND/OR → `getSingleFormula` heap-shaped binary tree (me & child 2i & child 2i+1), NOT a flat Nary.
- ExprCall inlines the body with an env of `cset(args)`; 0-arity functions are cached per Func (`cacheForConstants`), and recursive calls obey `Options.unrolls`.
- isIn/isInBinary: arrow multiplicities expand to quantified formulas with fresh `v<cnt>` variables (am=true).
- ExprQt: desugar (disj), addOne (unary decl without multiplicity → ONEOF), one/lone → comprehension.one/lone when all decls are unary ONEOF, else LONE = all/all pairs; guards for non-unary decls.

## Licensing & Resolved Caveats

- **100% pure MIT licensing**: `crates/satsolver/src/sat4j.rs` (SAT4J 2.3.1, LGPL-2.1/EPL-1.0) and `crates/kodkod` have been removed. All workspace crates are pure MIT (see `THIRD_PARTY_LICENSES.md`).
- **Single unified pipeline**: dual-pipeline divergence (`ALLOY_RS_NO_EXACT`, separate `translate.rs` vs `exact.rs` paths) is eliminated. Every command executes through `exact/` + `pardinus` + `BatSat`, with `Options.{symmetry, skolem_depth, no_overflow, unrolls}` wired end to end and runtime pre-BVE CNF + SBP-free circuit verification on every SAT model.
