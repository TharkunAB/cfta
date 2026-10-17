"""Verify the bounded gate/Scan source review and exact source excerpts."""
import hashlib
import json
from pathlib import Path
import re

p = Path(__file__).resolve().parent
root = p.parents[2]
m = json.loads((p / "guard-scan-manifest.json").read_text())
assert len(m["entries"]) == m["entry_count"]
for item in m["entries"]:
    assert hashlib.sha256((root / item["path"]).read_bytes()).hexdigest() == item["sha256"], item
s = json.loads((p / "guard-scan-sources.json").read_text())
assert s["source_count"] == len(s["entries"]) == 20
text = (p / "guard-scan-headers.md").read_text()
blocks = re.findall(r"## ([^ \n]+) — [^\n]+\n\n```(?:lean|haskell)\n(.*?)\n```", text, re.S)
assert len(blocks) == 48, len(blocks)
for name, body in blocks:
    lines = (root / name).read_text().splitlines()
    for numbered in body.splitlines():
        number, exact = numbered.split(": ", 1)
        assert lines[int(number) - 1] == exact, (name, number)
print(f"PASS: {m['entry_count']} hashes; 20 reviewed sources; 48 exact header/source excerpts")
