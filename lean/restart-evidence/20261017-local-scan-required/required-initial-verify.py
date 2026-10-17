#!/usr/bin/env python3
"""Verify the frozen uncapped Required evidence without writing files."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / "required-initial-manifest.json").read_text())
for entry in manifest["entries"]:
    data = (ROOT / entry["path"]).read_bytes()
    assert len(data) == entry["bytes"], entry["path"]
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]

for module, prefix, attempt, jobs in [
    ("SourceCurrentRequiredGuard", "required-guard", 1, 1125),
    ("SourceCurrentRequiredInitialNumeric", "required-initial", 2, 1565),
]:
    source = ROOT / "lean/MicroCFTA" / (module + ".lean")
    snapshot = HERE / f"{prefix}-direct-{attempt}.source.lean"
    assert source.read_bytes() == snapshot.read_bytes(), module
    assert (HERE / f"{prefix}-direct-{attempt}.log").stat().st_size == 0
    metadata = json.loads((HERE / f"{prefix}-direct-{attempt}.json").read_text())
    assert metadata["exit"] == 0
    assert metadata["command"][-1] == str(snapshot)
    canonical = (HERE / f"{prefix}-canonical-1.log").read_text()
    assert f"Build completed successfully ({jobs} jobs)." in canonical
    assert json.loads((HERE / f"{prefix}-canonical-1.json").read_text())["exit"] == 0

total = 0
for prefix, kind, attempt, count in [
    ("required-guard", "public", 1, 4),
    ("required-initial", "public", 1, 6),
    ("required-initial", "kernels", 2, 2),
]:
    stem = f"{prefix}-{kind}-{attempt}"
    assert json.loads((HERE / (stem + ".json")).read_text())["exit"] == 0
    log = (HERE / (stem + ".log")).read_text()
    assert not re.search(r"\bsorryAx\b|: (?:error|warning)(?:\(|:)", log), stem
    declarations = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log, re.S)
    declarations += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", log)]
    assert len(declarations) == count, stem
    source = (HERE / (stem + ".source.lean")).read_text()
    for name, axioms in declarations:
        axes = re.sub(r"\.\{[^}]*\}", "", axioms)
        assert {x.strip() for x in axes.split(",") if x.strip()} <= {
            "propext", "Classical.choice", "Quot.sound"
        }, (name, axes)
        assert f"#check @{name}" in source
        assert f"#print {name}" in source
        assert re.search(re.escape(name) + r"(?:\.\{[^}]*\})?\s*:", log), name
    total += count
assert total == 12
print(f"PASS: {len(manifest['entries'])} frozen entries; 10 public + 2 kernel pairs")
