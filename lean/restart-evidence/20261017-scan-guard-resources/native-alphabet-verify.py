#!/usr/bin/env python3
"""Verify the frozen finite alphabet component without writing files."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / "native-alphabet-manifest.json").read_text())
for entry in manifest["entries"]:
    data = (ROOT / entry["path"]).read_bytes()
    assert len(data) == entry["bytes"], entry["path"]
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]
source = ROOT / "lean/MicroCFTA/SourceCurrentNativeGuardAlphabet.lean"
assert source.read_bytes() == (HERE / "native-alphabet-direct-2.source.lean").read_bytes()
assert (HERE / "native-alphabet-direct-2.log").stat().st_size == 0
for phase in ("direct-2", "canonical-1", "public-1", "kernels-1"):
    assert (HERE / f"native-alphabet-{phase}.exit").read_text().strip() == "0", phase
for phase, expected in (("public", 19), ("kernels", 2)):
    text = (HERE / f"native-alphabet-{phase}-1.log").read_text()
    assert not re.search(r"(?:error:|warning:|sorryAx|declaration uses 'sorry')", text), phase
    reports = re.findall(r"depends on axioms: \[([^\]]*)\]", text)
    assert len(reports) == expected, (phase, len(reports))
    for report in reports:
        assert set(re.findall(r"[A-Za-z_][A-Za-z_0-9.]*", re.sub(r"\.\{[^}]*\}", "", report))) <= {"propext", "Classical.choice", "Quot.sound"}
    declarations = manifest["public_names"] if phase == "public" else manifest["kernel_names"]
    for name in declarations:
        assert re.search(re.escape(name) + r"(?:\.\{[^}]*\})?\s*:", text), name
canonical = (HERE / "native-alphabet-canonical-1.log").read_text()
assert "Build completed successfully (999 jobs)." in canonical
print(f"PASS {len(manifest['entries'])} entries; public 19 + kernels 2 pairs")
