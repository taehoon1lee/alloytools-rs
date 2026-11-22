//! Dev tool: translates Java-dumped Kodkod problems (`tools/exact/out/*.kk`) with the exact pipeline and compares
//! the SAT-solver call sequence with the Java trace (`*.cnf`, first block).
//!
//! cargo run --release -p pardinus --example kk_cnf -- tools/exact/out/X.kk [more.kk ...] [-v]

use pardinus::cnf::CnfSink;
use std::io::{BufRead, BufReader};

#[derive(Default)]
struct Rec {
    calls: Vec<String>,
    vars: i32,
}

impl CnfSink for Rec {
    fn num_vars(&self) -> i32 {
        self.vars
    }
    fn add_variables(&mut self, n: i32) {
        self.vars += n;
        self.calls.push(format!("v {n}"));
    }
    fn add_clause(&mut self, lits: &[i32]) {
        let mut s = String::from("c");
        for l in lits {
            s.push(' ');
            s.push_str(&l.to_string());
        }
        self.calls.push(s);
    }
}

fn java_calls(path: &str) -> Vec<String> {
    let f = std::fs::File::open(path).expect("open cnf");
    let mut out = Vec::new();
    for line in BufReader::new(f).lines() {
        let line = line.unwrap();
        if line == "begin" {
            continue;
        }
        if line == "end" || line.starts_with("s ") {
            break;
        }
        out.push(line);
    }
    out
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let verbose = args.iter().any(|a| a == "-v");
    if args.iter().any(|a| a == "--roundtrip") {
        let n = args.iter().filter(|a| a.ends_with(".kk")).filter(|a| !roundtrip(a)).inspect(|a| println!("roundtrip differs: {a}")).count();
        println!("roundtrip failures: {n}");
        return;
    }
    let (mut ok, mut bad) = (0, 0);
    for path in args.iter().filter(|a| a.ends_with(".kk")) {
        let text = std::fs::read_to_string(path).expect("read kk");
        let cnf_path = path.trim_end_matches(".kk").to_string() + ".cnf";
        let want = java_calls(&cnf_path);
        let res = std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn(move || -> Result<Vec<String>, String> {
                let mut p = pardinus::instance::read_kk(&text)?;
                let mut rec = Rec::default();
                pardinus::translator::translate(&mut p, &mut rec)?;
                Ok(rec.calls)
            })
            .unwrap()
            .join();
        let got = match res {
            Ok(Ok(c)) => c,
            Ok(Err(e)) => {
                bad += 1;
                println!("ERR  {path}: {e}");
                continue;
            }
            Err(_) => {
                bad += 1;
                println!("PANIC {path}");
                continue;
            }
        };
        if got == want {
            ok += 1;
            if verbose {
                println!("OK   {path} ({} calls)", got.len());
            }
        } else {
            bad += 1;
            let first = got.iter().zip(want.iter()).position(|(a, b)| a != b).unwrap_or(got.len().min(want.len()));
            println!(
                "DIFF {path}: rust {} calls, java {} calls, first difference at #{first}: rust={:?} java={:?}",
                got.len(),
                want.len(),
                got.get(first),
                want.get(first)
            );
        }
    }
    println!("cnf identical: {ok}, different: {bad}");
}

#[allow(dead_code)]
fn roundtrip(path: &str) -> bool {
    let text = std::fs::read_to_string(path).unwrap();
    let p = pardinus::instance::read_kk(&text).unwrap();
    let back = pardinus::kkwrite::write_kk(&p);
    back == text
}
