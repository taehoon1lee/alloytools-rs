# Java → Rust map

Roots: `CORE` = `reference/alloy-java/org.alloytools.alloy.core/src/main/java/edu/mit/csail/sdg`,
`KK` = `reference/alloy-java/org.alloytools.pardinus.core/src/main/java/kodkod`.
Sizes are Java line counts (to plan how many iterations a port takes). Update the Rust column as you go.

## Front-end → `crates/alloy-core`
| Java | lines | Rust | notes |
|---|---|---|---|
| `org.alloytools.alloy.core/parser/Alloy.lex` | 257 | `lexer.rs` | JFlex spec: token list, keywords, comments |
| `org.alloytools.alloy.core/parser/Alloy.cup` | 1159 | `parser.rs` | CUP grammar; precedence table at the top; actions call CompModule |
| `CORE/parser/CompModule.java` | 2721 | `module.rs`, `resolve.rs` | module building, opens, sig/func/fact/command resolution |
| `CORE/parser/CompUtil.java` | 484 | `lib.rs` | `parseEverything_fromFile`, recursive file loading |
| `CORE/parser/CompFilter.java` | 465 | `lexer.rs`, `parser.rs` | token post-processing: `!in` merge in `parser.rs` (`compare_level`), quantifier detection and `one ->` arrows in `parser.rs`; `run`/`check` labels still TODO (M2) |
| `CORE/parser/Macro.java` | ~150 | `resolve.rs` | `let` macros |
| `CORE/ast/Expr*.java` | ~4000 | `ast.rs` | resolved expression IR + `resolve()` typing |
| `CORE/ast/Type.java` | 1305 | `types.rs` | relational types (union of product types) |
| `CORE/ast/Sig.java` | 1059 | `ast.rs` | sig hierarchy, fields |
| `CORE/ast/Command.java`, `CommandScope.java` | 389 | `lib.rs` (`CommandInfo`) | `toString()` is what `scope_string` must equal |
| `CORE/ast/Func.java`, `Decl.java`, `Attr.java` | ~700 | `ast.rs` | |
| `CORE/alloy4/{Pos,Err,ErrorSyntax,ErrorType,ErrorFatal}.java` | small | `error.rs` | done |
| `org.alloytools.alloy.core/src/main/resources/models/util/*.als` | | `lib/util/*.als`, `stdlib.rs` | done (embedded) |

## Translator → `crates/alloy-translate`
| Java | lines | Rust | notes |
|---|---|---|---|
| `CORE/translator/TranslateAlloyToKodkod.java` | 1623 | `translate.rs` | visitor Alloy Expr → Kodkod node; `execute_command` (l.558) |
| `CORE/translator/ScopeComputer.java` | 538 | `scope.rs` | per-sig scopes, bitwidth, maxseq |
| `CORE/translator/BoundsComputer.java` | 505 | `bounds.rs` | atoms, lower/upper bounds, sig/field relations |
| `CORE/translator/A4Solution.java` | 2209 | `solution.rs` | holds bounds/formula/solver; `solve` (~l.1500+), `next` (l.1829), atom naming |
| `CORE/translator/Simplifier.java` | 338 | `simplify.rs` | partial-instance inference |
| `CORE/translator/A4Options.java` | ~200 | `lib.rs` (`Options`) | defaults: symmetry 20, skolemDepth 0, unrolls -1 |

## Kodkod / Pardinus → `crates/kodkod`
| Java | lines | Rust | notes |
|---|---|---|---|
| `KK/ast/*` | 5261 | `ast.rs` | Relation, Variable, Expression, Formula, IntExpression, Decls |
| `KK/instance/*` | 3432 | `instance.rs` | Universe, Tuple(Set/Factory), Bounds, Instance, TemporalInstance |
| `KK/engine/bool/*` | 5952 | `bool/` | `BooleanFactory`, `CBCFactory` (structural hashing), `BooleanMatrix`, `TwosComplementInt` |
| `KK/engine/fol2sat/Translator.java` | 777 | `fol2sat/mod.rs` | pipeline: flatten → skolemize → sym-break → FOL2Bool → CNF |
| `KK/engine/fol2sat/FOL2BoolTranslator.java` | 1120 | `fol2sat/fol2bool.rs` | core translation |
| `KK/engine/fol2sat/LeafInterpreter.java` | 328 | `fol2sat/leaf.rs` | primary variable allocation (ORDER MATTERS for stats parity) |
| `KK/engine/fol2sat/Bool2CNFTranslator.java` | 413 | `fol2sat/cnf.rs` | Tseitin encoding |
| `KK/engine/fol2sat/SymmetryDetector.java`, `SymmetryBreaker.java` | ~900 | `fol2sat/symmetry.rs` | |
| `KK/engine/fol2sat/Skolemizer.java` | 607 | `fol2sat/skolem.rs` | |
| `KK/engine/fol2sat/FormulaFlattener.java`, `FOL2BoolCache.java` | ~580 | `fol2sat/` | |
| `KK/engine/Evaluator.java` | 297 | `eval.rs` | |
| `KK/engine/Solver.java`, `PardinusSolver.java`, `Solution.java` | | `engine.rs` | |
| `KK/engine/ltl2fol/*` | 1993 | `ltl2fol/` | temporal → FOL unrolling |
| `KK/engine/TemporalPardinusSolver.java` | 1112 | `engine_temporal.rs` | trace-length iteration |
| `KK/engine/satlab/SATSolver.java` | | `crates/satsolver` | done (trait + BatSat) |
| `KK/util/ints/*` | | `util.rs` | IntSet/IntVector → Rust Vec/bitsets |
