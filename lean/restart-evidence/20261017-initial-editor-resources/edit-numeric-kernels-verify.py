#!/usr/bin/env python3
"""Verify concrete edit kernels and their explicit recovery provenance."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / "edit-numeric-kernels-manifest.json").read_text())
assert len(manifest["entries"]) == manifest["entry_count"]
seen = set()
for entry in manifest["entries"]:
    assert entry["path"] not in seen
    seen.add(entry["path"])
    data = (ROOT / entry["path"]).read_bytes()
    assert len(data) == entry["bytes"], entry["path"]
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]
source = (ROOT / manifest["source"]).read_text()
assert source == (HERE / "edit-numeric-kernels.lean").read_text()
assert "namespace MicroCFTA.EditNumericIntegration" in source
assert "private noncomputable def level := sizeOf edits" in source
log = (ROOT / manifest["log"]).read_text()
assert not re.search(r"error(?:\(|:)|warning:|sorryAx|truncated|maximum.*(?:depth|steps)", log)
pairs = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.M | re.S)
assert len(pairs) == 2
assert {name for name, _ in pairs} == {
    "MicroCFTA.EditNumericIntegration.constructed_mixed_edit",
    "MicroCFTA.EditNumericIntegration.constructed_compiled_forest",
}
assert len(re.findall(r"^#print axioms ", source, re.M)) == 2
assert len(re.findall(r"^#check @", source, re.M)) == 2
for name, axioms in pairs:
    assert "#print axioms " + name in source
    assert "#check @" + name in source
    assert re.search(r"^@?" + re.escape(name) + r"\s*:", log, re.M), name
    names = [re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in axioms.split(",") if item.strip()]
    assert set(names) <= {"propext", "Classical.choice", "Quot.sound"}, (name, names)
for setting in ["pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.universes true",
                "pp.deepTerms true", "pp.maxSteps 10000000", "linter.all true"]:
    assert "set_option " + setting in source
assert source.endswith("\n") and not source.endswith("\n\n")
assert manifest["missing_original_raw_log"] == "edit-numeric-kernels-1.log"
assert manifest["collision_artifacts_are_validation"] is False
recovery = (HERE / "edit-numeric-evidence-recovery.md").read_text()
assert "original attempt 1 full raw log is unavailable" in recovery
assert "Attempt 14" in recovery
print("PASS:", manifest["entry_count"], "hashes; 2 concrete complete pairs; diagnostics 0; original raw log loss explicit")
