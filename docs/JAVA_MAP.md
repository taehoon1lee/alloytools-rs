# Java → Rust map

Roots: `CORE` = `reference/alloy-java/org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg`,
`KK` = `reference/alloy-java/org.alloytools.pardinus.core/src/main/java/kodkod`.
Sizes are Java line counts (to plan how many iterations a port takes). Update the Rust column as you go.

## Front-end → `crates/alloy-core`
| Java | lines | Rust | notes |
|---|---|---|---|
| `org.alloytools.alloy.core/parser/Alloy.lex` | 257 | `lexer.rs` | JFlex spec: token list, keywords, comments |
| `org.alloytools.alloy.core/parser/Alloy.cup` | 1159 | `parser.rs` | CUP grammar; precedence table at the top; actions call CompModule |
| `CORE/parser/CompModule.java` | 2721 | `module.rs`, `sema.rs`, `loader.rs` | module building, opens, sig/func/fact/command resolution |
| `CORE/parser/CompUtil.java` | 484 | `lib.rs`, `loader.rs` | `parseEverything_fromFile`, recursive file loading |
| `CORE/parser/CompFilter.java` | 465 | `lexer.rs`, `parser.rs` | token post-processing: `!in` merge in `parser.rs` (`compare_level`), quantifier detection and `one ->` arrows |
| `CORE/parser/Macro.java` | ~150 | `sema.rs`, `exact/visit.rs` | `let` macros (substituted lazily as expressions) |
| `CORE/ast/Expr*.java` | ~4000 | `sema.rs`, `types.rs` | resolved expression IR + `resolve()` typing + `jtype` |
| `CORE/ast/Type.java` | 1305 | `types.rs`, `jtype.rs` | relational types (union of product types) |
| `CORE/ast/Sig.java` | 1059 | `sema.rs` | sig hierarchy, fields |
| `CORE/ast/Command.java`, `CommandScope.java` | 389 | `lib.rs` (`CommandInfo`) | `toString()` is what `scope_string` must equal |
| `CORE/ast/Func.java`, `Decl.java`, `Attr.java` | ~700 | `sema.rs` | |
| `CORE/alloy4/{Pos,Err,ErrorSyntax,ErrorType,ErrorFatal}.java` | small | `error.rs` | done |
| `org.alloytools.alloy.core/src/main/resources/models/util/*.als` | | `lib/util/*.als`, `stdlib.rs` | done (embedded) |

## Translator → `crates/alloy-translate`
| Java | lines | Rust | notes |
|---|---|---|---|
| `CORE/translator/TranslateAlloyToKodkod.java` | 1623 | `exact.rs`, `exact/{facts,visit}.rs`, `resolve.rs` | visitor Alloy Expr → Pardinus AST; `execute_command` / `count_solutions` in `lib.rs` |
| `CORE/translator/ScopeComputer.java` | 538 | `scope.rs` | per-sig scopes, bitwidth, maxseq |
| `CORE/translator/BoundsComputer.java` | 505 | `exact/bounds.rs` | atoms, lower/upper bounds, sig/field relations, symbolic bounds |
| `CORE/translator/A4Solution.java` | 2209 | `exact/instance.rs`, `exact.rs` | setup, solving, atom renaming (`rename`), sig/field/skolem evaluation |
| `CORE/translator/Simplifier.java` | 338 | `exact/simplify.rs` | partial-instance inference |
| `CORE/translator/A4Options.java` | ~200 | `lib.rs` (`Options`) | defaults: `symmetry=20`, `skolem_depth=0`, `no_overflow=false`, `unrolls=-1` (all wired) |

## Kodkod / Pardinus → `crates/pardinus` & `crates/satsolver`
| Java | lines | Rust | notes |
|---|---|---|---|
| `KK/ast/*` | 5261 | `pardinus/src/ast.rs`, `annotate.rs`, `replace.rs` | Relation, Variable, Expression, Formula, IntExpression, Decls |
| `KK/instance/*` | 3432 | `pardinus/src/instance.rs` | Universe, Tuple, TupleSet, Bounds, Options, Problem |
| `KK/engine/bool/*` | 5952 | `pardinus/src/bool.rs` | `Factory` (`CBCFactory` flat pool + structural hashing), `eval_bv`, `BooleanMatrix`, two's complement `Int`, `DefCond` |
| `KK/engine/fol2sat/Translator.java` | 777 | `pardinus/src/translator.rs` | `resolve`, `translate_circuit`, `emit_cnf`, `solve_portfolio` (4-thread `BatSat` + model verification), `count_all`/`count_projected`, `first_instance` |
| `KK/engine/fol2sat/FOL2BoolTranslator.java` + `LeafInterpreter.java` + `FOL2BoolCache.java` | ~2000 | `pardinus/src/fol2bool.rs` | core translation, primary variable allocation, node caching |
| `KK/engine/fol2sat/Bool2CNFTranslator.java` | 413 | `pardinus/src/cnf.rs` | iterative polarity + Plaisted-Greenbaum CNF, `SolverSink`, `ClauseBuffer`, `verify_cnf_model` |
| `KK/engine/fol2sat/SymmetryDetector.java`, `SymmetryBreaker.java` | ~900 | `pardinus/src/symmetry.rs` | partition detection (`JHashMap`), matrix symmetry breaking, `SbpOrder` (`JavaOrder`/`ArityDecl`/`DeclOrder`/`NoSbp`) |
| `KK/engine/fol2sat/Skolemizer.java` | 607 | `pardinus/src/replace.rs` | skolemization (`skolem_depth`) & predicate inlining |
| `KK/engine/Evaluator.java` | 297 | `pardinus/src/translator.rs` (`evaluate`) | constant expression evaluation |
| `KK/engine/ltl2fol/*`, `KK/engine/TemporalPardinusSolver.java` | ~3100 | `pardinus/src/temporal.rs` | LTL2FOL, `TemporalBoundsExpander`, `solve` (portfolio + max-length probe), `canonical_lasso`, `count_solutions` |
| `KK/engine/satlab/SATSolver.java` | | `crates/satsolver` + `crates/batsat` | pure-Rust `BatSat` (binary watches + `simp.rs` variable elimination + model extension) |

## Where things actually live now (2026-11-24)
| Java | Rust |
|---|---|
| `CompModule.resolveModules` (merge identical instances) | `alloy-core/src/loader.rs` `merge_instances` |
| `CompModule.populate` (name resolution, penalties, `this.f`) | `alloy-core/src/sema.rs` `name`, `field_ref`, `lookup_any`; `jtype.rs` `check_calls` |
| `ExprChoice` resolution by type | `alloy-translate/src/resolve.rs` + `exact/resolve.rs` |
| `BoundsComputer` + `ScopeComputer` + `Simplifier` | `alloy-translate/src/scope.rs`, `exact/bounds.rs`, `exact/simplify.rs` |
| `TranslateAlloyToKodkod` (`makeFacts`, `visitThis`, `isIn`) | `alloy-translate/src/exact.rs`, `exact/facts.rs`, `exact/visit.rs` |
| `SymmetryDetector` / `SymmetryBreaker` | `pardinus/src/symmetry.rs` (`partition`, `break_matrix_symmetries`, `generate_sbp`, `SbpOrder`) |
| `Skolemizer` (`skolemDepth`) & `PredicateInliner` | `pardinus/src/replace.rs` |
| `FOL2BoolTranslator` + `CBCFactory` + `Bool2CNFTranslator` | `pardinus/src/fol2bool.rs`, `bool.rs`, `cnf.rs` |
| Portfolio solving + verification + `--count` | `pardinus/src/translator.rs` (`solve_portfolio`, `verify_cnf_model`, `eval_bv`, `count_all`, `count_projected`, `first_instance`) |
| Temporal solving + counting | `pardinus/src/temporal.rs` (`ltl2fol`, `expand`, `solve`, `canonical_lasso`, `count_solutions`) |
| `A4Solution` atom renaming & evaluation | `alloy-translate/src/exact/instance.rs` |
| SAT solver (replacing SAT4J) | `satsolver` (`BatSat` over vendored `batsat` with binary watches, positive/negative initial polarities, geometric/Luby restarts, `simp.rs` BVE) |
