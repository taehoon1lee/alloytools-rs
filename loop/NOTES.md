# NOTES — durable knowledge (keep bullets short; newest at the bottom of each section)

## Environment
- Windows 11, Rust stable via rustup, host `x86_64-pc-windows-gnu`, **no C compiler** → pure-Rust crates only.
- `cargo` lives in `%USERPROFILE%\.cargo\bin`; add to PATH if a shell does not see it.
- Java 25 (only for the oracle). Alloy reference jar: `reference/bin/org.alloytools.alloy.dist.jar` (6.2.0).
- On Windows the Java launcher expands `*` arguments as file globs — irrelevant for us (oracle has no wildcard args).

## Harness facts
- Goldens were produced with `TranslateAlloyToKodkod.execute_command` (NOT `execute_commandFromBook`), SAT4J,
  symmetry 20, skolemDepth 0, per-command timeout 60s, sequential (-j1) on this machine.
- Java timings include JVM/JIT cold start per file (first command of a file is the slowest).
- `temporal` in goldens = `A4Solution.getMinTrace() != -1`.
- Instances are informational only: different SAT solvers legitimately find different instances.
- Corpus golden status: 194 ok, 4 type_error, 1 syntax_error (natural.als: duplicate alias).
  Commands: 238 UNSAT, 215 SAT, 12 ERROR (higher-order quantification not skolemizable), 1 Java TIMEOUT (unscored). 19 temporal commands.
- Java SAT/UNSAT total time over the corpus ~286 s; dominated by hotel4 NoBadEntry (47 s), p306-hotel NoIntruder (24 s), temporal buffer (21-24 s).

## Java quirks (add as you discover them)
- Anonymous command labels: `run$N` / `check$N` with N = 1 + number of commands already added (CompModule ~l.1951).
- `Command.toString()` is at `CORE/ast/Command.java` ~l.137; scopes print like `3 Prisoner, exactly 2 X`.

- Lexer (Alloy.lex): longest match, ties -> earlier rule. `1_000` is a "Name cannot start with a number" error
  (name rule ties with decimal and wins). Hex `0x` digits come in pairs (`0xa_b` is an error, `0xab_cd` ok).
- Lexer emits raw `!` `=` for `!=`, `!` `in` for `!in`; the parser must merge them (Java Filter class).
- `Version.experimental = true`, so string literals are accepted. Java keeps the quote chars inside the string
  value; our `Tok::Str` stores the content without quotes (keep this in mind when comparing string constants).

- Expression precedence (CUP call chain, loosest first): `;` (trace seq, right) < `||` < `<=>` < `=>`/`else` (right)
  < `&&` < `until/since/releases/triggered` < prefix `!` `always`.. < `=` `in` `<` `>` `<=` `>=` (+ `!` forms)
  < `<<` `>>` `>>>` < `+` `-` (+ `fun/add`,`fun/sub`) < `fun/mul`,`fun/div`,`fun/rem` < prefix `#`/`sum`/`int`
  < `++` < `&` < `->` (right) < `<:` < `:>` < `.` and `[]` (same level, left) < prefix `~` `*` `^` < postfix `'`.
  So `a + b & c` = `a + (b & c)` and `a.b[c]` = `c.(a.b)`.
- Quantifier keywords (`all no some lone one sum`) are quantifiers only when a `[private] [disj] names :` follows
  and the previous token is not `:` / `disj` (CompFilter). Otherwise they are multiplicity prefixes (`x: one A`).
- `A set -> some B`: multiplicity keywords between/after `->` are merged into the arrow (CompFilter). `A -> set B` == `A -> B`.
- `-1` merges into a number literal only in primary position (CompFilter rule: not after `) ] } ID NUMBER ...`).

## Design decisions
- Surface AST (`syntax.rs`): `c => a else b` is `ExprKind::IfElse`; `a !in b` / `a != b` have no own BinOp —
  build `Unary(Not, Binary(In|Equals))` like Java's `ExprUnary.Op.NOT` wrapping. `a[b]` stays `BoxJoin` until M3.
- SAT backend: `satsolver::BatSat` (pure-Rust MiniSat-like). Java baseline uses SAT4J (Java MiniSat-like).

- Expression parser (`parser.rs`): one method per CUP level, no precedence table. Surface conventions are listed in
  the module doc (e.g. `{}` = TRUE, `disj[..]`/`pred/totalOrder[..]` = `BoxJoin(Name(..))`, `int[e]`/`e.int` = `IntCast`).
- Paragraph parser (`parse_module`): `Super` blocks are `Vec<Expr>` conjuncts; `a; b c` is parsed by `super_p` as
  `a` and `after({b; c})` (Java `SuperP`), NOT by `expr()` (which would make `after(b)` and leave `c` at time 0).
  `pred`/`fun` bodies are `Block(conjuncts)`; `{}` = `Block([])` = TRUE. Sig-local names are kept as `Sig.name`.
  `sig A = B` is `SigExtends::Equal` (Java marker `"="`), `in` is `SigExtends::In`, `extends` is `SigExtends::Extends`.
- Labelled commands (`L: run {..}`) exist in the corpus (Alloy 6 syntax); now parsed (M1.4b).
- Labelled commands: CompFilter rewrites `L: run` to `run L ...`; the label is the ID before the colon. `run L foo` / `run L {`
  means label L; `run foo` alone is a target. A following `Id :` is the next labelled paragraph, not a name.
- Scopes: `for N` is overall only when followed by nothing or `but`; `for 5 int`/`for 3 seq`/`for 2..4 steps` are typescopes.
  `int` and `Int` both set bitwidth. `N..M` is exact when N==M. `3:2 Node` = increment 2, end MAX (increment comes before the sig).
  The Java `c(...)` extraction (univ/int/seq/steps out of the list, dup errors) is done in the parser (`Parser::scope`).
- Labels for CommandInfo: explicit label, else the target name, else `run$N`/`check$N` (N = 1 + commands before it).
- Known gaps (not ported yet): `int[a, b]` multi-argument form (error for now); the `x = e` declaration form
  (`Declb EQUALS`, used for fields); multiplicity on `in`/`=` right operands is not rewritten to `*Of` forms (M3 must
  apply `CompModule.mult`).

- Module loading (`loader.rs`): `open` target not next to the file -> embedded library (`stdlib.rs`). `examples/algorithms/messaging`
  is embedded too (Java gets it from the distribution `models/`). Default alias = last segment if plain identifier and no args, else `open$N` renamed to that segment when free.
- OPEN QUESTION (natural.als): Java rejects `open util/integer as integer` ("same alias") even alone in a neutral module, but accepts `as foo`
  and no alias; `open util/ordering as integer` after `open util/integer as bar` is also rejected. The clash source is not in addOpen's
  visible state; investigate the `opens` map seeding in CompModule (~l.1370 `opens.clear()` pass) before porting.

- IMPLICIT `integer` OPEN (Java): every module except util/integer implicitly has `open util/integer as integer`; that is why
  `minus[a,b]` and `integer/minus` resolve without an open, and why an explicit `open ... as integer` is a syntax error (natural.als).
- Macros: `m[a,b]` is a call only if arity matches; `x.m[a]` passes the receiver first; a parameterless macro boxed with args is a join.
- Funcs: `x.f` / `x.f[a]` with f taking params = call with the receiver first (`p.grandpas`).
- Root module parameters (`module m[Addr]` as root) become free sigs.
- Corpus survey (`cargo test corpus_resolution_survey -- --nocapture`): 113 resolved, 2 unsupported (string constants, overloads with args), 1 expected Java error.

- Java name resolution: own names first; otherwise every public name of every reachable module (transitively through opens).
  Several candidates form ExprChoice, resolved by type (here: the receiver's atoms vs each candidate's owner). `sema::lookup_unqualified`.
- Inside a sig body (field decls, appended facts, sig-local funs) a field name of that sig (or an ancestor) means `this.f`.
  The right operand of an explicit `x.f` is never implicitly re-joined (`explicit_field`).
- Calls: `f[a,b]` is a call only if `f` has exactly that many parameters (`nparams`, known at declaration); otherwise a join.
  `x.f[a]` with `f` taking a receiver is a call with `x` first. Commands are resolved after all function bodies.
- `all disj x,y | f` is `(x != y) => f`; `some disj` is `(x != y) and f`.
- Set declarations (`x: set E`): existential = witness bits; universal = dual (not some not). A set-declaration quantifier under an
  effective universal quantifier is Java's "higher-order quantification that could not be skolemized" ERROR (polarity tracked).
- pred/totalOrder[elem, first, next] (native in Java): one first in elem, first in no predecessor, next inside elem x elem,
  every element except first has one predecessor, except last one successor, no cycles, all reachable from first.
- Integers: Int atoms are always in the universe (bitwidth 4 default); numbers in set position are singleton atoms.
  Arithmetic wraps; comparisons are signed bit-vector circuits.
- Encoding: polarity-aware (Plaisted-Greenbaum) CNF; lex-leader symmetry breaking on interchangeable atom pairs.

- OPEN (opt_spantree, 4 cmds Java UNSAT / Rust SAT): reduced repro is `tmp/ost2/algorithms/spanning-tree/v2.als`
  (Closure assertion without the implication, plus fact LegalTrans and fact TransIfPossible; each fact alone is SAT in both).
  Suspects: Let-bound set values inside `some adjProc | let nLvl = ... | {...}`, `lo/next[nLvl]`, or `*~` in SpanTreeAtState.

- PERF FINDINGS (addressBook1h cmd 3 "delUndoesAdd for 10 but 3 Book"; Java 17k clauses, Rust 168k):
  gates are mostly binary AND/OR, but ~1.3k AND gates with fan-in >= 64 (whole-matrix subset/equality per leaf) carry most
  clauses; single-gate IFF/ITE changes little (-5% vars). Symmetry breaking is needed (disabling it: 15 regressions).
  batsat options: phase_saving=0 helps this command (1.6 s vs 2.7 s) but hurts dijkstra Closure (20 s vs 12 s); no global win.
  Gate is flaky on this command (budget 3 s). Real fix: Kodkod-style simplification/sharing of whole-matrix formulas (M6).

## HARNESS ISSUES (write evidence here instead of editing harness/)
- Overloads: `Tr::resolve(expr, Exp)` filters `RExpr::Choice` candidates by static atom-type overlap (arity + common tuple; JoinLeft/JoinRight use last/first column). Calls are filtered by arg-vs-param types.
- Fields are translated as `all this: owner | this.f in decl` (`in_formula`, Java `isIn` arrow multiplicities); `Field.this_local` is the local id of `this`.
- Skolemization (kodkod translator): `some`/negated `all` at positive polarity, not under a universal and not in Iff/ITE/comprehension -> fresh bits per variable (+ one-constraint). Matches Java skolemDepth=0 (primary vars +N).
- `util/ordering`: Java BoundsComputer/SymmetryBreaker pin Ord.First/Next to constants when the elem atoms are interchangeable (alloy-translate `pin_total_orders`); module header `[exactly elem]` forces the sig exact (`Model.exact_sigs`).
- Perf lesson: unrolled existentials (2700 leaves) were the cause of addressBook1h/dijkstra slowness; a fix in circuit shape beats solver tuning.
- SAT perf lessons: batsat Luby restarts were 5x slower than geometric on hard UNSAT (ceilingsAndFloors); Java's truncated SBP (20 bit pairs, rels sorted by arity,name)
  makes iolus 4x faster than full lex-leader but slows SAT puzzles (handshake) -> portfolio: 400ms no-SBP attempt first. Plain Tseitin vs polarity encoding: no difference.
- Java `Equals`: int equality only when BOTH sides are int-typed, else set equality; `+`/`-` are always set union/difference (ints via plus/minus funcs).
- Java sig allocation: abstract sig with children has no relation (union of children); non-abstract parent adds `<label>_remainder`; primary var counts match Java exactly now.
- Name visibility (CompModule.populate): inside a field decl only own/ancestor fields (as `this.f`) and no funcs; elsewhere all fields visible.
- Java merges module instances (same file, same resolved params): `util/ordering[Tick]` opened in two files is ONE ordering (`CompModule.resolveModules`). Ported in `loader::merge_instances`.
- `ty()` must iterate `local_bound` in sorted order (HashMap order made overload resolution nondeterministic).
- Portfolio budgets are load-sensitive (time-based limits under -j8); keep the first attempt small (15k conflicts / 800ms).
- SAT: initial polarity TRUE (batsat `new_var(lbool::TRUE, true)`) is ~3-10x faster than the default on the hard UNSAT corpus models (likely SAT4J's default phase); best single config = SBP order0 + geometric restarts + pol TRUE.
- Portfolio: after a 200ms conflict-capped SBP attempt, 4 configs race on threads (first answer sets a stop flag). Heavy-tailed SAT time makes this the practical lever; keep thread count <= 4 (gate runs -j8).
- File-level type errors: Java type-checks the root module at load; `--no-solve` runs `sema::build` and reports only `ErrorKind::Type` errors (identical-signature overloads etc.).
