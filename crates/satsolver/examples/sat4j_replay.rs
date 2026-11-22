//! Dev tool: replays SAT-solver call traces recorded from Java Alloy (tools/exact/TraceOracle.java) into the
//! SAT4J port and checks that the result and the full model are identical.
//!
//! cargo run --release -p satsolver --example sat4j_replay -- trace1.cnf [trace2.cnf ...]

use satsolver::sat4j::Sat4j;
use std::io::{BufRead, BufReader};

fn main() {
    let mut total_ok = 0;
    let mut total_bad = 0;
    for path in std::env::args().skip(1) {
        let f = std::fs::File::open(&path).expect("open trace");
        let mut s = Sat4j::new();
        let mut res: Option<bool> = None;
        let mut block = 0;
        let mut bad = Vec::new();
        let t0 = std::time::Instant::now();
        for line in BufReader::new(f).lines() {
            let line = line.unwrap();
            if line == "begin" {
                s = Sat4j::new();
                res = None;
            } else if let Some(n) = line.strip_prefix("v ") {
                s.add_variables(n.parse().unwrap());
            } else if line.starts_with('c') {
                let lits: Vec<i32> = line[1..].split_whitespace().map(|x| x.parse().unwrap()).collect();
                s.add_clause(&lits);
            } else if let Some(r) = line.strip_prefix("s ") {
                res = s.solve();
                let want = r == "SAT";
                if res != Some(want) {
                    bad.push(format!("block {block}: result {res:?} != {want}"));
                }
            } else if let Some(m) = line.strip_prefix("m ") {
                if res == Some(true) {
                    let diff = m.bytes().enumerate().filter(|(i, b)| s.value_of(*i as u32 + 1) != (*b == b'1')).count();
                    if diff > 0 {
                        bad.push(format!("block {block}: model differs in {diff} of {} vars", m.len()));
                    }
                }
            } else if line == "end" {
                block += 1;
            }
        }
        let ms = t0.elapsed().as_secs_f64() * 1000.0;
        if bad.is_empty() {
            total_ok += 1;
            println!("OK   {path} blocks={block} {ms:.1}ms");
        } else {
            total_bad += 1;
            println!("BAD  {path} {}", bad.join("; "));
        }
    }
    println!("files ok={total_ok} bad={total_bad}");
}
