//! Debug tool: solves a DIMACS CNF (e.g. one written with `KSAT_DUMP=<file>`) with the `BatSat` backend and prints
//! the answer, wall time and search statistics. Usage: `cargo run --release --example cnfbench -- <file.cnf>...`
//! The same `KSAT_*` environment knobs as in the CLI apply; `KSAT_POL=0|1` sets the initial polarity (default 1).

use satsolver::{BatSat, SatSolver};

fn main() {
    let pol = match std::env::var("KSAT_POL").ok().as_deref() {
        Some("0") => Some(false),
        Some("d") => None,
        _ => Some(true),
    };
    for path in std::env::args().skip(1) {
        let text = std::fs::read_to_string(&path).expect("read cnf");
        let mut s = BatSat::configured(false, 0.0, 0, pol);
        let mut clause: Vec<i32> = Vec::new();
        for line in text.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('c') {
                continue;
            }
            if let Some(rest) = line.strip_prefix("p cnf") {
                let n: u32 = rest.split_whitespace().next().unwrap().parse().unwrap();
                s.add_variables(n);
                continue;
            }
            for tok in line.split_whitespace() {
                let l: i32 = tok.parse().unwrap();
                if l == 0 {
                    s.add_clause(&clause);
                    clause.clear();
                } else {
                    clause.push(l);
                }
            }
        }
        // KSAT_SIMP=<n>: variable elimination with variables 1..=n frozen
        if let Some(n) = std::env::var("KSAT_SIMP").ok().and_then(|v| v.parse::<u32>().ok()) {
            let frozen: Vec<u32> = (1..=n).collect();
            s.set_simplify(&frozen);
        }
        let t0 = std::time::Instant::now();
        let r = s.solve();
        let dt = t0.elapsed();
        println!("{path}: {:?} {:.3}s {}", r, dt.as_secs_f64(), s.stats_line());
    }
}
