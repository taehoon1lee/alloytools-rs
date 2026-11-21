"""Preflight / bootstrap: makes sure reference sources, the Java jar, the oracle and the Rust toolchain exist.

Usage: python harness/setup.py   (idempotent; the loop driver runs it before starting)
"""
import os
import shutil
import subprocess
import sys
from pathlib import Path

from common import CORPUS_FILE, GOLDEN_DIR, JAR, ORACLE_CLASSES, REFERENCE, ROOT

ok = True


def step(msg, cond, fix=None):
    global ok
    if cond():
        print(f"[ok]   {msg}")
        return
    if fix:
        print(f"[fix]  {msg} ...")
        fix()
        if cond():
            print(f"[ok]   {msg}")
            return
    print(f"[FAIL] {msg}")
    ok = False


def run(cmd, cwd=ROOT):
    print("       $ " + " ".join(map(str, cmd)))
    subprocess.run(cmd, cwd=str(cwd), check=False)


REFERENCE.mkdir(exist_ok=True)
step("reference/alloy-java (Java source)", lambda: (REFERENCE / "alloy-java" / "settings.gradle").exists(),
     lambda: run(["git", "clone", "--depth", "1", "https://github.com/AlloyTools/org.alloytools.alloy.git",
                  str(REFERENCE / "alloy-java")]))
step("reference/models (sample models)", lambda: (REFERENCE / "models" / "README.md").exists(),
     lambda: run(["git", "clone", "--depth", "1", "https://github.com/AlloyTools/models.git", str(REFERENCE / "models")]))
step("reference/bin/org.alloytools.alloy.dist.jar (Alloy 6.2.0)", lambda: JAR.exists(),
     lambda: (JAR.parent.mkdir(parents=True, exist_ok=True),
              run(["gh", "release", "download", "v6.2.0", "-R", "AlloyTools/org.alloytools.alloy",
                   "-p", "org.alloytools.alloy.dist.jar", "-D", str(JAR.parent)])))
step("java on PATH", lambda: shutil.which("java") is not None)
step("java oracle compiled", lambda: (ORACLE_CLASSES / "AlloyOracle.class").exists(),
     lambda: (ORACLE_CLASSES.mkdir(parents=True, exist_ok=True),
              run(["javac", "-nowarn", "-encoding", "UTF-8", "-cp", str(JAR), "-d", str(ORACLE_CLASSES),
                   str(ORACLE_CLASSES.parent / "src" / "AlloyOracle.java")])))
cargo = shutil.which("cargo") or (Path.home() / ".cargo" / "bin" / ("cargo.exe" if os.name == "nt" else "cargo"))
step("cargo (Rust toolchain)", lambda: Path(cargo).exists())
step("harness/corpus.json", lambda: CORPUS_FILE.exists(), lambda: run([sys.executable, "harness/corpus.py"]))
step("harness/golden/*.json", lambda: GOLDEN_DIR.exists() and any(GOLDEN_DIR.glob("*.json")))
step("git repository", lambda: (ROOT / ".git").exists())
sys.exit(0 if ok else 1)
