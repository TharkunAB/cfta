"""Verify the final independent gate and seeded caller review."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

p = Path(__file__).resolve().parent
root = p.parents[2]
m = json.loads((p / "guard-scan-final-manifest.json").read_text())
assert len(m["entries"]) == m["entry_count"]
for item in m["entries"]:
    assert hashlib.sha256((root / item["path"]).read_bytes()).hexdigest() == item["sha256"], item
subprocess.run([sys.executable, str(p / "guard-scan-verify.py")], check=True)
for module, stem, jobs in [
    ("SourceCurrentGateGuard", "gate-guard", 0),
    ("SourceCurrentGateFrameResources", "gate-frame", 1532),
    ("SourceCurrentSeededCallerNumeric", "seeded-caller", 1535),
]:
    attempt = {"gate-guard": 1, "gate-frame": 3, "seeded-caller": 2}[stem]
    assert (p / f"{stem}-direct-{attempt}.log").stat().st_size == 0
    assert (p / f"{stem}-direct-{attempt}.source.lean").read_bytes() == (root / "lean/MicroCFTA" / (module + ".lean")).read_bytes()
    if jobs:
        assert f"Build completed successfully ({jobs} jobs)" in (p / f"{stem}-canonical-2.log").read_text()
text = (p / "guard-scan-final-headers.md").read_text()
blocks = re.findall(r"## ([^ \n]+) — [^\n]+\n\n```lean\n(.*?)\n```", text, re.S)
assert len(blocks) == 13, len(blocks)
for name, body in blocks:
    lines = (root / name).read_text().splitlines()
    for numbered in body.splitlines():
        number, exact = numbered.split(": ", 1)
        assert lines[int(number) - 1] == exact, (name, number)
print(f"PASS: {m['entry_count']} hashes; final adapters reviewed; 13 exact new headers; prior review retained")
