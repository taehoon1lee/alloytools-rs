"""Build harness/corpus.json: the list of .als sample models used for comparison.

Sources:
  reference/models                                         (github.com/AlloyTools/models)
  reference/alloy-java/org.alloytools.alloy.extra/extra/models  (examples bundled with Alloy)

Usage: python harness/corpus.py
"""
import json
import re

from common import CORPUS_FILE, REFERENCE

SOURCES = [
    ("models", REFERENCE / "models"),
    ("extra", REFERENCE / "alloy-java" / "org.alloytools.alloy.extra" / "extra" / "models"),
]

TEMPORAL_RE = re.compile(r"\bvar\b|\balways\b|\beventually\b|\bafter\b|\bbefore\b|\bhistorically\b|"
                         r"\bonce\b|\buntil\b|\breleases\b|\bsince\b|\btriggered\b|\bsteps\b|'")
COMMAND_RE = re.compile(r"^\s*(?:\w+\s*:\s*)?(run|check)\b", re.M)
COMMENT_RE = re.compile(r"//[^\n]*|--[^\n]*|/\*.*?\*/", re.S)


def main():
    entries = []
    for tag, base in SOURCES:
        for p in sorted(base.rglob("*.als")):
            rel = p.relative_to(base).with_suffix("").as_posix()
            text = p.read_text(encoding="utf-8", errors="replace")
            code = COMMENT_RE.sub("", text)
            entries.append({
                "id": f"{tag}/{rel}",
                "path": p.relative_to(REFERENCE.parent).as_posix(),
                "lines": text.count("\n") + 1,
                "temporal_hint": bool(TEMPORAL_RE.search(code)),
                "has_commands_hint": bool(COMMAND_RE.search(code)),
            })
    CORPUS_FILE.write_text(json.dumps(entries, indent=1), encoding="utf-8")
    print(f"{len(entries)} models -> {CORPUS_FILE}")


if __name__ == "__main__":
    main()
