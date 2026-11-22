"""Compare the Rust exact Alloy->Kodkod translation with Java's dumps (tools/exact/out, from trace_all.py).
usage: python tools/exact/cmp_alloy.py [--filter S] [--check-only]"""
import argparse, json, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "harness"))
from common import load_corpus  # noqa

ap = argparse.ArgumentParser()
ap.add_argument("--filter")
ap.add_argument("--check-only", action="store_true")
a = ap.parse_args()
corpus = {e["id"]: e["path"] for e in load_corpus()}
res = json.load(open(os.path.join(HERE, "out", "_trace_all.json")))
lines = []
for r in res:
    if a.filter and a.filter not in r["id"]:
        continue
    tag = r["id"].replace("/", "__") + f"#{r['index']}"
    if a.check_only:
        g = json.load(open(os.path.join(ROOT, "harness", "golden", r["id"].replace("/", "__") + ".json"), encoding="utf-8"))
        if [c for c in g["commands"] if c["index"] == r["index"]][0].get("kind") != "check":
            continue
    lines.append(f"{corpus[r['id']]}\t{r['index']}\t{os.path.join(HERE, 'out', tag)}")
exe = os.path.join(ROOT, "target", "release", "examples", "exact_cmp" + (".exe" if os.name == "nt" else ""))
p = subprocess.run([exe], input="\n".join(lines) + "\n", capture_output=True, text=True, encoding="utf-8", errors="replace", cwd=ROOT)
print(p.stdout[-20000:])
if p.stderr.strip():
    print(p.stderr[-2000:])
