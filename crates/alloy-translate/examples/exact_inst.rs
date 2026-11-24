//! Dev tool: runs the unified `pardinus` + `batsat` pipeline and prints the first instance
//! the way the Java oracle does. stdin lines: `<model.als>\t<command index>\t<tag>`; one JSON line per input.
//! cargo run --release -p alloy-translate --example exact_inst < list.txt

use std::io::BufRead;

fn q(s: &str) -> String {
    let mut o = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

fn run(model: &str, idx: usize) -> Result<String, String> {
    let world = alloy_core::parse_everything_from_file(std::path::Path::new(model)).map_err(|e| e.to_string())?;
    let m = alloy_core::sema::build(&world.modules).map_err(|e| e.to_string())?;
    let t = std::time::Instant::now();
    let r = alloy_translate::exact::solve_first(&world, &m, idx, &alloy_translate::Options::default(), None)
        .map_err(|e| e.to_string())?;
    let ms = t.elapsed().as_secs_f64() * 1000.0;
    let mut s = format!("\"sat\":{},\"ms\":{ms:.1}", r.sat);
    if let Some(states) = r.instance {
        s.push_str(&format!(",\"instance\":{{\"trace_length\":{},\"loop\":{},\"states\":[", states.len(), r.loop_state));
        for (si, inst) in states.iter().enumerate() {
            if si > 0 {
                s.push(',');
            }
            s.push('{');
            let mut first = true;
            for (k, v) in inst {
                if !first {
                    s.push(',');
                }
                first = false;
                s.push_str(&q(k));
                s.push_str(":[");
                let ts: Vec<String> = v.iter().map(|t| format!("[{}]", t.iter().map(|a| q(a)).collect::<Vec<_>>().join(","))).collect();
                s.push_str(&ts.join(","));
                s.push(']');
            }
            s.push('}');
        }
        s.push_str("]}");
    }
    Ok(s)
}

fn main() {
    for line in std::io::stdin().lock().lines() {
        let line = line.unwrap();
        let p: Vec<&str> = line.split('\t').collect();
        if p.len() != 3 {
            continue;
        }
        let (model, idx, tag) = (p[0].to_string(), p[1].parse::<usize>().unwrap(), p[2].to_string());
        let res = std::thread::Builder::new().stack_size(1 << 30).spawn(move || run(&model, idx)).unwrap().join();
        match res {
            Ok(Ok(s)) => println!("{{\"tag\":{},{s}}}", q(&tag)),
            Ok(Err(e)) => println!("{{\"tag\":{},\"error\":{}}}", q(&tag), q(&e[..e.len().min(300)])),
            Err(_) => println!("{{\"tag\":{},\"error\":\"panic\"}}", q(&tag)),
        }
    }
}
