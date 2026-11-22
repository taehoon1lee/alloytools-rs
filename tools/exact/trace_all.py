"""Record Java ground truth for the exact (Java-identical) pipeline, one entry per SAT command:
  out/<tag>.kk    Kodkod problem handed to PardinusSolver.solveAll (formula DAG + bounds + options)
  out/<tag>.cnf   SAT4J call trace (addVariables/addClause sequence + result + full model)
  out/<tag>.json  the Alloy instance exactly as harness/java-oracle prints it
and checks the instance against harness/golden (read-only) plus a SAT4J replay of the trace.

usage (repo root):  python tools/exact/build.py && python tools/exact/trace_all.py [check|all] [-j N] [--filter S]
Never used by Rust code; dev/verification only."""
import argparse, json, os, subprocess, sys, glob
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from common import GOLDEN_DIR, load_corpus  # noqa

CP = os.path.join(ROOT, "reference", "bin", "org.alloytools.alloy.dist.jar") + os.pathsep + os.path.join(HERE, "classes")
OUT = os.path.join(HERE, "out")


def tag(cid, idx):
    return cid.replace("/", "__") + f"#{idx}"


def java(args, timeout=900):
    return subprocess.run(["java", "-Xss64m", "-cp", CP] + args, capture_output=True, text=True, encoding="utf-8",
                          errors="replace", cwd=ROOT, timeout=timeout)


def job(a):
    cid, path, jc = a
    pre = os.path.join(OUT, tag(cid, jc["index"]))
    r = java(["edu.mit.csail.sdg.translator.KKDump", path, str(jc["index"]), pre])
    out = r.stdout.strip().splitlines()[:1]
    res = {"id": cid, "index": jc["index"], "dump": out[0] if out else f"FAIL rc={r.returncode}"}
    try:
        res["same_as_golden"] = json.load(open(pre + ".json", encoding="utf-8")) == jc.get("instance")
    except Exception as e:  # noqa
        res["same_as_golden"] = f"no json: {e}"
    r2 = java(["edu.mit.csail.sdg.translator.TraceOracle", "replay", pre + ".cnf"])
    res["replay"] = (r2.stdout.strip().splitlines() or ["?"])[-1]
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", nargs="?", default="check", choices=["check", "all"])
    ap.add_argument("-j", type=int, default=4)
    ap.add_argument("--filter")
    a = ap.parse_args()
    os.makedirs(OUT, exist_ok=True)
    corpus = {e["id"]: e["path"] for e in load_corpus()}
    jobs = []
    for f in sorted(glob.glob(str(GOLDEN_DIR / "*.json"))):
        g = json.load(open(f, encoding="utf-8"))
        if a.filter and a.filter not in g["file"]:
            continue
        for c in g.get("commands", []):
            if c.get("status") == "SAT" and (a.mode == "all" or c.get("kind") == "check"):
                jobs.append((g["file"], corpus[g["file"]], c))
    with ThreadPoolExecutor(a.j) as ex:
        res = list(ex.map(job, jobs))
    json.dump(res, open(os.path.join(OUT, f"_trace_{a.mode}.json"), "w"), indent=1)
    for r in res:
        if r["same_as_golden"] is not True or "bad=0" not in r["replay"]:
            print("PROBLEM", r)
    print(f"{len(res)} dumped; same_as_golden={sum(r['same_as_golden'] is True for r in res)} "
          f"replay_ok={sum('bad=0' in r['replay'] for r in res)}")


if __name__ == "__main__":
    main()
