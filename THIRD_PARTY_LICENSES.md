# Third-Party Licenses & Provenance

`alloy-rs` is a 100% pure-Rust, pure-MIT port of Alloy Analyzer 6.2.0 and Kodkod/Pardinus, with one vendored pure-Rust SAT backend (`batsat`). Upstream sources are pinned under `reference/alloy-java/` and documented in `docs/JAVA_MAP.md` and `docs/EXACT_PORT.md`.

## Upstream & Vendored Components

| Component | Upstream / Reference Source | Rust Location | License |
|---|---|---|---|
| **Alloy Analyzer 6.2.0** | `reference/alloy-java/org.alloytools.alloy.core` ([Alloy.txt](reference/alloy-java/org.alloytools.alloy.dist/LICENSES/Alloy.txt)) | `crates/alloy-core`, `crates/alloy-translate` | **MIT** (incl. MIT no-endorsement clause) |
| **Kodkod / Pardinus** | `reference/alloy-java/org.alloytools.pardinus.core` ([Kodkod.txt](reference/alloy-java/org.alloytools.pardinus.core/LICENSE)) | `crates/pardinus` | **MIT** |
| **batsat 0.6.0** (vendored, modified in-tree) | `github.com/c-cube/batsat` (`crates/batsat/Cargo.toml`) | `crates/batsat`, `crates/satsolver` | **MIT** |

## Licensing Status & Distribution Notice

1. **100% pure MIT workspace**:
   Every crate in the workspace (`alloy-core`, `pardinus`, `satsolver`, vendored `batsat`, `alloy-translate`, and `alloy-cli`) is licensed solely under **MIT**. The earlier SAT4J 2.3.1 port (`sat4j.rs`, LGPL-2.1 / EPL-1.0) and legacy `crates/kodkod` crate have been removed; `alloy-rs` solves all static and temporal problems via `crates/pardinus` + `crates/satsolver` (`BatSat`) with runtime CNF and circuit verification.
2. **MIT no-endorsement notice**:
   Per `reference/alloy-java/org.alloytools.alloy.dist/LICENSES/Alloy.txt`, the name of the Massachusetts Institute of Technology must not be used in advertising or otherwise to promote this software without prior written authorization.
