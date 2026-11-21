# PROGRESS — append-only iteration log (max 6 lines per entry)

## 2026-11-21 M0 — environment built (Opus)
parse 0/199, commands 0/199, verdict 0/465, perf 0/465 (Rust returns `unsupported` everywhere)
next: M1.1 lexer

## 2026-11-21 M1.1 — lexer (`crates/alloy-core/src/lexer.rs`, longest-match like JFlex)
parse 0/199, commands 0/199, verdict 0/465, perf 0/465 (no parser yet; lexer unit tests + all 199+ corpus .als lex OK)
next: M1.2 surface AST (`syntax.rs`)

## 2026-11-21 M1.2 — surface AST (`crates/alloy-core/src/syntax.rs`, types only, no parsing yet)
parse 0/199, commands 0/199, verdict 0/465, perf 0/465 (unchanged; Rust still `unsupported`; 9 unit tests pass; gate exit 0)
next: M1.3 expression parser (precedence from Alloy.cup) producing `syntax::Expr`

## 2026-11-21 M1.3 — expression parser (`crates/alloy-core/src/parser.rs`, one fn per Alloy.cup level)
parse 0/199, commands 0/199, verdict 0/465, perf 0/465 (no paragraph parser yet; 19 alloy-core unit tests pass; gate exit 0)
Surface AST: added `Mult`, `BinOp::Arrow(Mult,Mult)`, `IntPlus/IntMinus`, `UnOp::IntCast`, `Const::IntMin/IntMax/IntNext`.
next: M1.4 declarations/paragraphs (sigs, fields via `Parser::decl`, facts, pred/fun, assert, run/check, open, enum, let)

## 2026-11-21 M1.4a — paragraph parser (`parse_module` in `parser.rs`: header, open, enum, sig, fact, assert, pred, fun)
parse 0/199, commands 0/199, verdict 0/465, perf 0/465 (`parse_everything_from_file` not wired yet; 26 alloy-core tests pass; gate exit 0)
Fixed M1.3 bug: `pred/totalOrder[..]` in primary position bumped 2 tokens instead of 3.
Corpus test: every file parses except run/check/let/labelled commands (Unsupported). Errors after the first command are not checked yet.
next: M1.4b run/check/labelled commands + `let` macros + `x = e` field form, then wire `parse_everything_from_file` (`World::commands`)

## 2026-11-21 M1.4b/M1.5 — commands, macros, `f = e` fields; parse 194/199 (acceptance met)
parse 194/199, commands 0/199, verdict 0/465, perf 0/465 (`parse_everything_from_file` = root module only; `scope_string` empty)
Parse misses are Java module/type errors (natural dup alias = M2.1; integer/seqrel/sequniv/sequence type errors = M3). 30 alloy-core tests; strict corpus parse test; gate exit 0.
next: M2.1 module loading (`open`, params, aliases) then M2.2/M2.3 commands (labels, Command.toString)

## 2026-11-21 M2.2/M2.3/M2.4 — command headers: Command.toString, default `Run Default`, labels; commands 194/199 (acceptance met)
parse 194/199, commands 194/199, verdict 0/465, perf 0/465 (`command_to_string`/`scope_entry_to_string` in lib.rs mirror Command.java toString + CommandScope.toString; no-command module gets Java's `Default`)
next: M2.1 module loading (natural.als dup alias; `open` resolution), then M3 semantics

## 2026-11-21 M2.1 — module loader (`loader.rs`): opens resolved relative to the file, else embedded library; parse 194/199
parse 194/199, commands 194/199, verdict 0/465, perf 0/465 (opened modules are loaded into `World::modules`; no semantics yet)
Embedded `examples/algorithms/messaging` (ringlead needs it). natural.als alias error still open (see NOTES).
next: M3.1 resolved sig hierarchy / fields (semantic model)

## 2026-11-21 M3.1-3.3 — resolved model (`sema.rs`) + implicit `integer` open; parse 195/199, commands 195/199
parse 195/199, commands 195/199, verdict 0/465, perf 0/465 (no typing/translation yet). Survey: 113/116 models resolve.
Also: loader adds Java's implicit `open util/integer as integer` (explains natural.als syntax error; now matches Java).
next: M3.4 typing (arity, Choice resolution by type), then M4 kodkod core

## 2026-11-21 M4/M5 first translation — kodkod engine + Alloy→Kodkod translator end-to-end; verdict 117/465
parse 195/199, commands 195/199, verdict 117/465 (no wrong answers except 3 under investigation), perf 103/465
kodkod: instance/ast/bool (hash-consed Tseitin gates)/translate (FOL2Bool, quantifiers unrolled, closure, solve+decode); 8 tests.
alloy-translate: scope.rs (ScopeComputer + atom creation with Java unique names), translate.rs (sig/field constraints, formulas, calls).
Java facts learned: universe always has Int atoms (bitwidth 4, `-8..7`), Int relation exact; enum sigs scope 0; unique names append `'`.
next: decl-type errors (61 cmds, INSLabel), arity of calls (iolus), `=` arity (file_system), closure errors, pred/totalOrder, arrow mults, then integers

## 2026-11-21 M5 fixes — verdict 122/465 (gate green; 0 wrong answers in the last run)
Fixes: set declarations (witness bits; `all` by duality), arrow-multiplicity join order (`a.(this.f)`), transitive unqualified
name lookup + type-based choice of overloaded names (Java getRawNQS/ExprChoice), param bounds for typing.
Kodkod: Plaisted-Greenbaum polarity encoding (BoolFactory::finish), lex-leader symmetry breaking on interchangeable atoms.
next: integers (Card/IntNext/comparisons/sum: ~80 cmds), pred/totalOrder, arrow mults in expressions, lone/some decls, perf (M6).

## 2026-11-21 integers + name/arity fixes — verdict 154/465 (gate green, 0 wrong answers)
Integers (bit-vector Int in kodkod, IntExpr/IntCmp, numbers as singleton atoms); dot/box calls need matching arity;
commands resolved after all functions (param counts known at declaration); higher-order `some x: set S` nested under
universal quantifiers reported as Java's ERROR (polarity tracked in alloy-translate); abstract sig scope from children.
next: ExprChoice on non-receiver positions, pred/totalOrder, decl-type errors (syncimpl), arrow mults in expressions, lone/some decls.

## 2026-11-21 status — verdict 196/465 (gate green), perf 154/465, parse 195/199, commands 195/199
Open: (1) overloaded box calls `f[x]` with several candidates -> ExprChoice by argument types (patch saved in tmp/overload_choice.patch;
it is correct but makes dijkstra-K-state Closure (16 s) and addressBook1h delUndoesAdd (2.4 s) too slow for the harness budget;
needs M6 perf first). (2) opt_spantree 4 cmds wrong (see NOTES). (3) temporal (M8, ~19 cmds), --count (M7), perf (M6).

## 2026-11-21 typing/skolem/ordering — verdict 277/465 (gate green), perf 249/465, timeouts 21 -> 3
Done: field decl types (this/Call/Compr), overload resolution by static atom-type (`Tr::ty/resolve/resolve_pair/resolve_join`),
`in_formula` with nested arrow multiplicities (fields = `all this: O | this.f in decl`), Kodkod-style skolemization (depth 0; kodkod `skolemize`),
`module m[exactly A]` params forced exact, `breakTotalOrder` port (util/ordering relations pinned to constants, Ord.First/Next 0 primary vars).
next: overload ambiguity (einstein: `this.(prev+next)`, 56 cmds), `join arity 1,1` (philosophers, 28), flipflop "no candidate" (17), `min[..]` with args (12).

## 2026-11-21 name resolution/SBP/solver — verdict 412/465 (gate green)
Done: Java `populate` visibility in field decls, `Int[e]`, restrict-operator overloads, field `disj`, implicit `one` on unary field bounds,
`Equals` int-vs-set semantics (+/- are set ops), `allocatePrimSig` (abstract sigs = union of children, `_remainder` rel), facts in positive polarity,
higher-order arrow-bound decl vars, kodkod static_arity of outer vars, Java `generateSBP` (20 bit pairs, rels sorted by arity+name),
geometric restarts (SAT4J-like), restart portfolio in `kodkod::translate::solve` (no-SBP 400ms -> Java SBP -> alt order).
Remaining 53: temporal (~21, M8), lone/some decl mult (5), `=`/union arity (6), hotel3/4 overloads (4), javatypes (4), p306-hotel/ceilings perf, misc.
next: perf (--perf), remaining non-temporal failures, then M8 temporal.

## 2026-11-21 module merge/sum/div/lone-some — verdict 425/465 (gate green)
Done: Java `resolveModules` port (`loader::merge_instances`: same file + same canonical sig args = one module instance, so two `open util/ordering[Tick]` share one ordering),
`sum x: e | i` (IntExpr::SumOver), signed div/rem circuits, `x: lone/some e` decl vars, multi-var `lone/one`, bare-name overloads skip arg-taking funcs.
Remaining 40: temporal (~21), hotel3/4 (4 overload), javatypes_soundness (4), INSLabel (2 higher-order), view-backing/stable-orient-ring (arity), basic-auth (strings), perf-heavy (p306-hotel, ceilings).

## 2026-11-21 strings/seq/size/INSLabel — verdict 442/465 (gate green)
Done: Java size constraints (`#sig <= n` / `= n`), string literals (String atoms + per-literal relations), `seq` keyword (+implicit sequniv open), sig links pre-pass,
penalty-aware ExprChoice (one-element Choice marks penalty 1), `run f` on functions, first-column field constraint as join (not a univ^k product: 15 s -> ms), portfolio clock starts at solve().
Remaining 23: temporal (21 cmds in extra/examples/temporal: buffer, leader, leader_events, trash), p306-hotel NoIntruder (perf, Java 24 s).
