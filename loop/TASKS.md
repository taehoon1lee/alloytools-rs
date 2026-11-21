# TASKS — Alloy (Java) → Rust port

Work top to bottom. One `[ ]` per iteration. Split big tasks into sub-bullets when you start them.
Each milestone ends with a harness acceptance criterion; a milestone is done when it is met.
Scores come from `python harness/check.py` (see CLAUDE.md). Java paths are relative to
`reference/alloy-java/` (abbrev: `CORE` = `org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg`,
`KK` = `org.alloytools.pardinus.core/src/main/java/kodkod`).

## M0 — Environment (done by the environment builder)
- [x] Java oracle, golden outputs, corpus (199 models, 465 Java-decided commands), harness, loop driver
- [x] Rust workspace skeleton; CLI implements the harness protocol; SAT backend `satsolver::BatSat`

## M1 — Lexer + parser (crate `alloy-core`)
Reference: `org.alloytools.alloy.core/parser/Alloy.lex`, `.../parser/Alloy.cup` (grammar + precedence),
`CORE/parser/CompModule.java` (what each grammar action builds).
- [x] M1.1 Token enum + lexer (`lexer.rs`): keywords, identifiers (letters, digits, `_`, `'`, `"`, `$`, `/`
      handling as in Alloy.lex), numbers (decimal, hex `0x`, binary `0b`), string literals, comments
      (`//`, `--`, `/* */`, `/** */`), all operators (`=>`, `<=>`, `->`, `<:`, `:>`, `++`, `.`, `#`, `~`, `^`, `*`,
      `!`, `!=`, `!in`, `<<`, `>>`, `>>>`, `'` prime, `;`, `@` …). Positions = (line, col) 1-based like `Pos`.
      Unit tests incl. a test that lexes every `reference/**/*.als` without error.
- [x] M1.2 Surface AST (`syntax.rs`): module header, `open` (with args + alias), `sig` (abstract/one/lone/some/
      var/private, extends/in, fields with multiplicities, appended fact), `enum`, `fact`, `pred`, `fun`,
      `assert`, `run`/`check` (label, body or name, scopes, `but`, `exactly`, `int`, `seq`, `steps`, `expect`),
      macros (`let` at top level), expressions (all operators of Alloy 6 incl. temporal).
- [x] M1.3 Expression parser (Pratt / precedence climbing) mirroring the precedence in Alloy.cup
      (`||`/or < `<=>` < `=>`/else < `&&` < `!` < temporal binary < … < `.` / `[]` box join). Unit tests that
      check the parse tree of tricky expressions (`a.b[c]`, `all x: A | p => q else r`, `x' = y`, `#a + 1`).
- [ ] M1.4 Declarations/paragraph parser. `parse_everything_from_file` returns `Ok(World)` with commands
      (labels/scopes can be approximate until M2). Syntax errors -> `ErrorKind::Syntax` with Pos.
- [ ] M1.5 Make every corpus file parse: `python harness/check.py` → **parse ≥ 194/199** (only the
      type_error files may still differ).

## M2 — Modules + command headers (parity of the `commands` level)
Reference: `CORE/parser/CompModule.java` (`addCommand`, `addOpen`, `resolveCommands`, ~line 1900-2100),
`CORE/parser/CompUtil.java` (`parseRecursively`, file lookup), `CORE/ast/Command.java` (`toString` ~l.137),
`CORE/ast/CommandScope.java`.
- [ ] M2.1 Module loading: `open a/b[X] as c` relative to the root file's directory, else the embedded
      `alloy_core::stdlib`; module parameters; aliases; detect duplicate aliases (natural.als → syntax_error).
- [ ] M2.2 Commands: anonymous labels exactly as Java (`run$N`/`check$N` where N = 1 + number of commands
      before it), only the root module's commands, `expect`, `CommandInfo` fields equal to Java
      (`overall`, `bitwidth`, `maxseq`, `minprefix`, `maxprefix` defaults = -1 when not given).
- [ ] M2.3 `scope_string` == Java `Command.toString()` (incl. `exactly`, sig names without `this/`, `steps`).
- [ ] M2.4 Acceptance: **commands ≥ 194/199**.

## M3 — Semantic model: sigs, fields, name resolution, type checking
Reference: `CORE/ast/{Sig,Field,Decl,Func,Expr*,Type}.java`, `CORE/parser/CompModule.java`
(`resolveSigs`, `resolveFieldDecl`, `resolveFuncDecls`, `resolveFacts`, `resolveAssertions`), `ExprBadCall`, `ExprChoice`.
- [ ] M3.1 Resolved sig hierarchy (`univ`, `Int`, `seq/Int`, `String`, `none`; abstract/one/lone/some/var; `extends`/`in`
      subset sigs; enum sigs); field declarations with multiplicity; module parameter instantiation.
- [ ] M3.2 Resolved expression IR (separate from surface AST): ExprVar, ExprUnary, ExprBinary, ExprList,
      ExprQt, ExprLet, ExprITE, ExprCall, ExprConstant, Sig/Field references, temporal operators.
- [ ] M3.3 Name resolution incl. overloading (`ExprChoice`), implicit `this` in sig facts/fields, `@` names,
      function/predicate calls with box join `f[x]`, macros.
- [ ] M3.4 Type checking (`Type.java`): relation arity/types; ambiguity and unresolved-name errors as `Type`
      errors. Acceptance: the 4 `type_error` files match; parse = 199/199.

## M4 — Kodkod core (crate `kodkod`, test it standalone first)
Reference: `KK/ast`, `KK/instance`, `KK/engine/bool`, `KK/engine/fol2sat`, `KK/engine/Solver.java`.
- [ ] M4.1 `instance`: Universe, Tuple, TupleSet (bitset of tuple indices), TupleFactory, Bounds (lower/upper per
      relation, int bounds), Instance.
- [ ] M4.2 `ast`: Relation, Variable, ConstantExpression (UNIV, IDEN, NONE, INTS), Expression ops (join, product,
      union, intersection, difference, override, transpose, closure, reflexive closure, comprehension, ite,
      projection), Formula (and/or/not/implies/iff, in/eq, multiplicity, quantifiers, constant true/false),
      IntExpression (constant, cardinality, sum, arithmetic, comparisons, IntToExprCast/ExprToIntCast). Hash-consed arena.
- [ ] M4.3 `bool`: BooleanFactory (gates AND/OR/NOT/ITE with structural hashing like `CBCFactory`), BooleanMatrix
      (dense/sparse, dot/union/intersection/closure), Int (two's complement, `TwosComplementInt`).
- [ ] M4.4 `fol2sat`: FOL2BoolTranslator for relations + formulas (no ints), LeafInterpreter (bounds -> primary vars
      in the SAME ORDER as Java), Bool2CNFTranslator (Tseitin/polarity as Java), solve with `satsolver`,
      decode the model into an Instance. Unit tests: small problems (pigeonhole UNSAT, simple graph SAT).
- [ ] M4.5 Ints in fol2sat: bitwidth, IntConstant, cardinality, sum, plus/minus/mul/div/mod, comparisons, Int casts.
- [ ] M4.6 Evaluator (evaluate an expression/formula on an Instance) — used for instances and debugging.

## M5 — Alloy → Kodkod (crate `alloy-translate`): first real verdicts
Reference: `CORE/translator/{TranslateAlloyToKodkod,ScopeComputer,BoundsComputer,A4Solution,Simplifier}.java`.
- [ ] M5.1 ScopeComputer: default scope 3, `but`, `exactly`, one/lone/some sigs, abstract sigs, subsigs, `Int`
      bitwidth default 4, `seq` default; same error messages for invalid scopes.
- [ ] M5.2 BoundsComputer: atoms named exactly like Java (`Sig$0`…), lower/upper bounds per sig and field,
      `Int` atoms, partial instance inference (`inferPartialInstance`), `util/ordering` handling if Java special-cases it.
- [ ] M5.3 TranslateAlloyToKodkod for facts, sig/field constraints (multiplicities, disjointness, appended facts),
      pred/fun inlining, `run` = facts ∧ pred body, `check` = facts ∧ ¬assert. Simplest corpus models SAT/UNSAT correct.
- [ ] M5.4 Quantifiers + `disj`, comprehension, let, ITE, closure, cardinality, integers, `sum`, `seq`.
- [ ] M5.5 Higher-order quantifier errors as Java (`ERROR` commands in s_ringlead, ins).
- [ ] M5.6 Acceptance: **verdict ≥ 90% of non-temporal commands**; then drive the rest of the static failures to 0.

## M6 — Performance parity (Rust must not be slower than Java)
Compare `stats.primary_vars` / `vars` / `clauses` with Java in `--verbose`; equal numbers = equal translation.
- [ ] M6.1 Symmetry breaking: `KK/engine/fol2sat/SymmetryDetector.java`, `SymmetryBreaker.java` (lex-leader, `symmetry=20`).
- [ ] M6.2 Skolemizer (`Skolemizer.java`) incl. `skolemDepth`; FormulaFlattener; sharing/caching (`FOL2BoolCache`).
- [ ] M6.3 Simplifier / partial-instance inference parity (`Simplifier.java`).
- [ ] M6.4 Profile the slowest commands (`--perf`, top of the perf failure list); optimize hot paths
      (TupleSet bitsets, BooleanMatrix, hash-consing). Consider SAT backend tuning or a custom CDCL only if
      solve_ms dominates.
- [ ] M6.5 Acceptance: **perf == verdict** (every verdict-correct command at most 1.1×Java+20ms).

## M7 — Solution enumeration
- [ ] M7.1 `Solution::next()` like `A4Solution.next()` (block primary variables, re-solve incrementally).
- [ ] M7.2 Acceptance: `python harness/check.py --count` (symmetry=0 counts) matches Java on all scored commands.

## M8 — Alloy 6 temporal logic (var sigs/fields, LTL, `steps`)
Reference: `KK/engine/ltl2fol/{LTL2FOLTranslator,TemporalTranslator,TemporalBoundsExpander}.java`,
`KK/engine/TemporalPardinusSolver.java`, `CORE/translator/TranslateAlloyToKodkod.java` (temporal parts).
- [ ] M8.1 Temporal AST nodes in kodkod + translation of `var` sigs/fields.
- [ ] M8.2 Bounded LTL → FOL unrolling with lasso traces, trace length iteration `min_trace..max_trace` like Pardinus.
- [ ] M8.3 Acceptance: all temporal commands' verdicts match.

## M9 — Error parity & polish
- [ ] M9.1 Syntax/type error line+col equal to Java (check `error_line_match` in results/latest.json).
- [ ] M9.2 Everything green: parse/commands/verdict/perf all at 100% of what Java decides; `--count` green.
