#!/usr/bin/env python3
"""Verify the frozen Seeded guard producer component without writing files."""
from pathlib import Path
import hashlib
import json
import re
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
m = json.loads((HERE / "seeded-guard-manifest.json").read_text())
for e in m["entries"]:
    data = (ROOT / e["path"]).read_bytes()
    assert len(data) == e["bytes"], e["path"]
    assert hashlib.sha256(data).hexdigest() == e["sha256"], e["path"]
for part, name, jobs in (("forecast", "SourceCurrentSeededGuardForecast", 1523),
                         ("numeric", "SourceCurrentSeededGuardNumeric", 1539)):
    assert (ROOT / f"lean/MicroCFTA/{name}.lean").read_bytes() == (HERE / f"seeded-guard-{part}-direct-1.source.lean").read_bytes()
    assert (HERE / f"seeded-guard-{part}-direct-1.log").stat().st_size == 0
    for stage in ("direct", "canonical"):
        assert (HERE / f"seeded-guard-{part}-{stage}-1.exit").read_text().strip() == "0"
    assert f"Build completed successfully ({jobs} jobs)." in (HERE / f"seeded-guard-{part}-canonical-1.log").read_text()
for phase, expected in (("public", 11), ("kernels", 2)):
    assert (HERE / f"seeded-guard-{phase}-1.exit").read_text().strip() == "0"
    text = (HERE / f"seeded-guard-{phase}-1.log").read_text()
    assert not re.search(r"error:|warning:|sorryAx|declaration uses 'sorry'", text), phase
    reports = re.findall(r"depends on axioms: \[([^\]]*)\]", text)
    assert len(reports) == expected, (phase, len(reports))
    for report in reports:
        names = re.findall(r"[A-Za-z_][A-Za-z_0-9.]*", re.sub(r"\.\{[^}]*\}", "", report))
        assert set(names) <= {"propext", "Classical.choice", "Quot.sound"}
    for name in m[f"{phase}_names"]:
        assert re.search(re.escape(name) + r"(?:\.\{[^}]*\})?\s*:", text), name
print(f"PASS {len(m['entries'])} entries; public 11 + kernels 2 pairs")
