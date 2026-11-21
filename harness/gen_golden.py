"""Generate golden (expected) outputs by running the official Java Alloy 6.2.0 on every corpus model.

This is run ONCE by the environment builder (Opus). The Haiku loop must NOT regenerate or edit goldens.

Usage:
  python harness/gen_golden.py                 # verdict/timing goldens -> harness/golden/
  python harness/gen_golden.py --count-mode    # solution-count goldens (symmetry=0) -> harness/golden_count/
Options: -j N (parallel jobs, default 1 so timings are clean), --timeout-ms, --filter SUBSTR, --force
"""
import argparse
import json
import time
from concurrent.futures import ThreadPoolExecutor

from common import (CP_SEP, GOLDEN_COUNT_DIR, GOLDEN_DIR, JAR, ORACLE_CLASSES, ROOT, eprint, golden_name,
                    last_json_line, load_corpus, run_proc)


def oracle_cmd(path, cid, timeout_ms, start, extra):
    return ["java", "-Xmx6g", "-XX:+UseSerialGC", "-cp", f"{JAR}{CP_SEP}{ORACLE_CLASSES}", "AlloyOracle",
            "--file", path, "--display-name", cid, "--timeout-ms", str(timeout_ms), "--start", str(start)] + extra


def run_one(entry, timeout_ms, extra):
    cid, path = entry["id"], entry["path"]
    start, merged = 0, None
    while True:
        rc, out, err, el = run_proc(oracle_cmd(path, cid, timeout_ms, start, extra), timeout_s=3600)
        doc = last_json_line(out)
        if doc is None:
            doc = {"schema": 1, "tool": "java-alloy-6.2.0", "file": cid, "status": "error",
                   "error": {"kind": "oracle_crash", "msg": (err or out)[-600:]}, "commands": []}
            if merged is None:
                merged = doc
            break
        if merged is None:
            merged = doc
        else:
            merged["commands"].extend(doc["commands"])
        if rc == 3 and doc["commands"]:
            start = doc["commands"][-1]["index"] + 1
            if start >= doc.get("command_count", 0):
                break
            continue
        break
    merged.pop("start", None)
    return merged


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("-j", type=int, default=1)
    ap.add_argument("--timeout-ms", type=int, default=None)
    ap.add_argument("--filter", default=None)
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--count-mode", action="store_true")
    ap.add_argument("--count", type=int, default=100)
    a = ap.parse_args()

    if a.count_mode:
        outdir = GOLDEN_COUNT_DIR
        timeout = a.timeout_ms or 20000
        extra = ["--symmetry", "0", "--count", str(a.count), "--no-instance"]
    else:
        outdir = GOLDEN_DIR
        timeout = a.timeout_ms or 60000
        extra = []
    outdir.mkdir(parents=True, exist_ok=True)

    corpus = [e for e in load_corpus() if not a.filter or a.filter in e["id"]]
    todo = [e for e in corpus if a.force or not (outdir / golden_name(e["id"])).exists()]
    eprint(f"{len(todo)}/{len(corpus)} models to run, timeout={timeout}ms, jobs={a.j}")

    t0 = time.time()

    def job(e):
        doc = run_one(e, timeout, extra)
        (outdir / golden_name(e["id"])).write_text(json.dumps(doc, indent=1), encoding="utf-8")
        st = [c.get("status") for c in doc.get("commands", [])]
        eprint(f"[{time.time() - t0:7.1f}s] {e['id']}: {doc.get('status')} {st}")

    with ThreadPoolExecutor(max_workers=a.j) as ex:
        list(ex.map(job, todo))
    eprint(f"done in {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
