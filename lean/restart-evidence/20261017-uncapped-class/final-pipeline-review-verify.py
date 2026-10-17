"""Check the frozen source-only local pipeline review."""
from pathlib import Path
import hashlib
import json
p = Path(__file__).resolve().parent
root = p.parents[2]
m = json.loads((p / "final-pipeline-review-manifest.json").read_text())
assert len(m["entries"]) == m["entry_count"]
assert len(m["new_modules"]) == 14
for entry in m["entries"]:
    raw = (root / entry["path"]).read_bytes()
    assert len(raw) == entry["bytes"], entry["path"]
    assert hashlib.sha256(raw).hexdigest() == entry["sha256"], entry["path"]
expected = {
    "SourceCurrentClassesNumeric": "029aea899480a96dae220fcd6d72e3bca5d5cf8537b292e8323c15e5664251e8",
    "SourceCurrentLocalNumeric": "e70403ae1da770e3a08ec4f4a7bf27bc28d06e5fca10248fd1da2b58ae750624",
}
for name, digest in expected.items():
    assert hashlib.sha256((root / ("lean/MicroCFTA/" + name + ".lean")).read_bytes()).hexdigest() == digest
print(f"PASS: {m['entry_count']} source/review hashes; 14 final modules; no new proof checks claimed")
