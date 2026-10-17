"""Verify the frozen gate and seeded caller resource adapters."""

import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
manifest = json.loads((evidence / "caller-resources-manifest.json").read_text())
assert len(manifest["entries"]) == manifest["entry_count"]
for entry in manifest["entries"]:
    assert hashlib.sha256((root / entry["path"]).read_bytes()).hexdigest() == entry["sha256"], entry["path"]
for module, attempt, canonical in [
    ("SourceCurrentGateGuard", "gate-guard-direct-1", "gate-guard-canonical-1.log"),
    ("SourceCurrentGateFrameResources", "gate-frame-direct-3", "gate-frame-canonical-2.log"),
    ("SourceCurrentSeededCallerNumeric", "seeded-caller-direct-2", "seeded-caller-canonical-2.log"),
]:
    assert (evidence / f"{attempt}.log").stat().st_size == 0
    assert (root / f"lean/MicroCFTA/{module}.lean").read_bytes() == (evidence / f"{attempt}.source.lean").read_bytes()
    output = (evidence / canonical).read_text()
    assert "Build completed successfully" in output
    assert not re.search(r"error:|warning: MicroCFTA/SourceCurrent", output)
print(f"PASS: {manifest['entry_count']} hashes; three final strict logs empty; canonical targets pass")
