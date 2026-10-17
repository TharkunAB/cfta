#!/usr/bin/env python3
"""Verify the frozen independent numeric Scan caller checks without writes."""
from pathlib import Path
import hashlib
import json
import re
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
m = json.loads((HERE / "scan-caller-plan-manifest.json").read_text())
for e in m["entries"]:
    data = (ROOT / e["path"]).read_bytes()
    assert len(data) == e["bytes"], e["path"]
    assert hashlib.sha256(data).hexdigest() == e["sha256"], e["path"]
for mod, snap, jobs in (("SourceCurrentScanNumeric", "scan-numeric-direct-4", 1582),
                        ("SourceCurrentScanCallerNumeric", "scan-caller-direct-1", 1597)):
    assert (ROOT / f"lean/MicroCFTA/{mod}.lean").read_bytes() == (HERE / f"{snap}.source.lean").read_bytes()
    assert (HERE / f"{snap}.log").stat().st_size == 0
    label = "scan-numeric" if mod.endswith("ScanNumeric") else "scan-caller"
    assert f"Build completed successfully ({jobs} jobs)." in (HERE / f"{label}-canonical-1.log").read_text()
for phase, attempt, expected in (("public", 1, 1), ("kernels", 3, 2)):
    assert (HERE / f"scan-caller-plan-{phase}-{attempt}.exit").read_text().strip() == "0"
    text = (HERE / f"scan-caller-plan-{phase}-{attempt}.log").read_text()
    assert not re.search(r"error(?:[:(])|warning:|sorryAx|declaration uses 'sorry'", text), phase
    reports = re.findall(r"depends on axioms: \[([^\]]*)\]", text)
    assert len(reports) == expected
    for report in reports:
        names = re.findall(r"[A-Za-z_][A-Za-z_0-9.]*", re.sub(r"\.\{[^}]*\}", "", report))
        assert set(names) <= {"propext", "Classical.choice", "Quot.sound"}
    for name in m[f"{phase}_names"]:
        assert re.search(re.escape(name) + r"(?:\.\{[^}]*\})?\s*:", text), name
print(f"PASS {len(m['entries'])} entries; public 1 + kernels 2 pairs")
