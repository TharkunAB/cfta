#!/usr/bin/env python3
"""Verify the frozen read-only Scan plan and exact source excerpts."""
from pathlib import Path
import hashlib
import json
import re
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
m = json.loads((HERE / "scan-plan-manifest.json").read_text())
for e in m["entries"]:
    data = (ROOT / e["path"]).read_bytes()
    assert len(data) == e["bytes"], e["path"]
    assert hashlib.sha256(data).hexdigest() == e["sha256"], e["path"]
for h in json.loads((HERE / "scan-plan-headers.json").read_text()):
    lines = (ROOT / h["path"]).read_text().splitlines()
    assert "\n".join(lines[h["start"]-1:h["end"]]) + "\n" == h["text"], h["path"]
assert (HERE / "scan-plan-readprobe-1.exit").read_text().strip() == "0"
text = (HERE / "scan-plan-readprobe-1.log").read_text()
assert not re.search(r"error:|warning:|sorryAx", text)
assert text.count("MicroCFTA.") >= 20
print(f"PASS {len(m['entries'])} entries; 20 source files; 40 exact header excerpts; readprobe 20 signatures")
