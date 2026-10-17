#!/usr/bin/env python3
"""Verify the independent InitialRanges checks without writing files."""
from pathlib import Path
import hashlib
import json
import re
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
m = json.loads((HERE / "initial-ranges-check-manifest.json").read_text())
for e in m["entries"]:
    data = (ROOT / e["path"]).read_bytes()
    assert len(data) == e["bytes"], e["path"]
    assert hashlib.sha256(data).hexdigest() == e["sha256"], e["path"]
assert (ROOT / "lean/MicroCFTA/SourceCurrentSeededInitialRanges.lean").read_bytes() == (HERE / "seeded-initial-ranges-direct-2.source.lean").read_bytes()
assert (HERE / "seeded-initial-ranges-direct-2.log").stat().st_size == 0
assert "Build completed successfully (1532 jobs)." in (HERE / "seeded-initial-ranges-canonical-1.log").read_text()
for phase in ("public", "kernels"):
    assert (HERE / f"initial-ranges-check-{phase}-1.exit").read_text().strip() == "0"
    text = (HERE / f"initial-ranges-check-{phase}-1.log").read_text()
    assert not re.search(r"error:|warning:|sorryAx|declaration uses 'sorry'", text), phase
    reports = re.findall(r"depends on axioms: \[([^\]]*)\]", text)
    assert len(reports) == 2
    for report in reports:
        names = re.findall(r"[A-Za-z_][A-Za-z_0-9.]*", re.sub(r"\.\{[^}]*\}", "", report))
        assert set(names) <= {"propext", "Classical.choice", "Quot.sound"}
    for name in m[f"{phase}_names"]:
        assert re.search(re.escape(name) + r"(?:\.\{[^}]*\})?\s*:", text), name
print(f"PASS {len(m['entries'])} entries; public 2 + kernels 2 pairs")
