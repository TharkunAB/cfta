"""Verify the frozen initial ordered edit scans producer without rebuilding."""

import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
manifest = json.loads((evidence / "edit-scans-manifest.json").read_text())
assert manifest["entry_count"] == len(manifest["entries"])
for entry in manifest["entries"]:
    data = (root / entry["path"]).read_bytes()
    assert len(data) == entry["bytes"], entry["path"]
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]
source = root / "lean/MicroCFTA/SourceCurrentConstrainedCapEditScans.lean"
assert source.read_bytes() == (evidence / "edit-scans-direct-3.source.lean").read_bytes()
assert (evidence / "edit-scans-direct-3.log").read_bytes() == b""
assert "Build completed successfully (1541 jobs)." in (evidence / "edit-scans-canonical-1.log").read_text()
probe = (evidence / "edit-scans-public.lean").read_text()
log = (evidence / "edit-scans-public-1.log").read_text()
assert not re.search(r"error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|\.\.\.", log)
names = re.findall(r"^#print axioms (\S+)", probe, re.M)
assert len(names) == len(re.findall(r"^#check @", probe, re.M)) == 4
for name in names:
    assert "#check @" + name in probe and name in log, name
blocks = re.findall(r"depends on axioms: \[([^\]]*)\]", log, re.S)
assert len(blocks) + log.count("does not depend on any axioms") == 4
for block in blocks:
    axioms = {re.sub(r"\.\{[^}]+\}", "", name.strip()) for name in block.split(",") if name.strip()}
    assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, axioms
for setting in ["linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]:
    assert "set_option " + setting in probe, setting
print(f"PASS: {len(manifest['entries'])} hashes; complete initial ordered edit scans; four full public pairs; strict clean; canonical pass; standard axioms")
