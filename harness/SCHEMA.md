# Harness JSON protocol (schema 1)

Both the Java oracle (`harness/java-oracle/src/AlloyOracle.java`) and `alloy-rs exec --json` print ONE JSON
document per invocation on stdout. Key order is irrelevant.

## File document
| key | type | meaning |
|---|---|---|
| `schema` | 1 | |
| `tool` | string | `java-alloy-6.2.0` / `alloy-rs-x.y.z` |
| `file` | string | corpus id (from `--display-name`) |
| `status` | `ok` \| `syntax_error` \| `type_error` \| `error` \| `unsupported` \| `crash` | outcome of parse+resolve+typecheck |
| `error` | null \| `{kind, line, col, in_file, msg}` | file-level error (line/col 1-based, -1 unknown) |
| `parse_ms` | number | |
| `command_count` | int | number of root-module commands (only when status = ok) |
| `commands` | array | command documents (only those that were run) |

## Command document
| key | meaning |
|---|---|
| `index` | 0-based position in `World::commands()` |
| `label`, `kind` (`run`/`check`), `expects`, `scope`, `overall`, `bitwidth`, `maxseq`, `minprefix`, `maxprefix` | header; must equal Java (`scope` = `Command.toString()`) |
| `status` | `SAT` \| `UNSAT` \| `ERROR` \| `TIMEOUT` \| `UNSUPPORTED` \| `CRASH` \| `NOT_RUN` (with `--no-solve`) |
| `error` | null \| `{kind, line, col, in_file, msg}` |
| `temporal`, `min_trace`, `max_trace` | temporal problem info (`min_trace == -1` ⇒ static) |
| `translate_ms`, `solve_ms`, `total_ms` | timing; **`total_ms` is what perf compares** |
| `stats` | `{primary_vars, vars, clauses}` as reported to `A4Reporter.solve` |
| `instance` | first instance (if SAT and not `--no-instance`): `{trace_length, loop, states:[{rel: [[atom..]..]}]}`; keys `this/Sig`, `this/Sig.field`, `skolem:$x` |
| `count`, `count_capped`, `count_ms` | with `--count N`: number of solutions enumerated (≤ N) |

## Invocation
```
alloy-rs exec --json --file F --display-name ID --no-solve
alloy-rs exec --json --file F --display-name ID --command I --timeout-ms MS
alloy-rs exec --json --file F --display-name ID --command I --timeout-ms MS --symmetry 0 --count 100 --no-instance
```
Exit code 3 ⇒ a command timed out (document still printed). The harness additionally enforces a process
timeout and records `TIMEOUT`/`CRASH` itself.
