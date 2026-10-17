"""Verify the bounded final Scan source review registry."""
import hashlib
import json
from pathlib import Path
p = Path(__file__).resolve().parent
root = p.parents[2]
m = json.loads((p / "scan-final-review-manifest.json").read_text())
assert len(m["entries"]) == m["entry_count"]
for e in m["entries"]:
    b = (root / e["path"]).read_bytes()
    assert len(b) == e["bytes"]
    assert hashlib.sha256(b).hexdigest() == e["sha256"], e
s = json.loads((p / "scan-final-review-sources.json").read_text())
assert len(s["sources"]) == s["source_count"]
assert s["sources"][0]["sha256"] == "81276597659270a613ad5b6c216c661e6c50ba97e249beffebe75391a619b772"
assert s["sources"][1]["sha256"] == "e522f913246a692d310c48c1f25c121798adb9592457a272118aa3ebd3dcc013"
for e in s["sources"]:
    assert hashlib.sha256((root / e["path"]).read_bytes()).hexdigest() == e["sha256"]
print(f"PASS: {m['entry_count']} hashes; {s['source_count']} reviewed source pins; no new theorem or test claimed")
