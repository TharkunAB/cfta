#!/usr/bin/env python3
"""Verify the frozen normalized source comparison and its capped evidence."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / "normalized-comparison-manifest.json").read_text())
for item in manifest["files"]:
    path = ROOT / item["path"]
    assert path.is_file(), item["path"]
    assert hashlib.sha256(path.read_bytes()).hexdigest() == item["sha256"], item["path"]

for module, strict, canonical, jobs in [
    ("SourceCurrentNativeNormalizedComparison", "normalized-comparison-direct-15", "normalized-comparison-canonical-1", 328),
    ("SourceCurrentNativeNormalizedComparisonInactive", "normalized-comparison-inactive-direct-2", "normalized-comparison-inactive-canonical-1", 330),
    ("SourceCurrentNativeNormalizedComparisonExecution", "normalized-comparison-execution-direct-15", "normalized-comparison-execution-canonical-1", 559),
]:
    production = ROOT / "lean" / "MicroCFTA" / (module + ".lean")
    assert production.read_bytes() == (HERE / (strict + ".source.lean")).read_bytes()
    metadata = json.loads((HERE / (strict + ".json")).read_text())
    assert metadata["exit_code"] == 0
    assert (HERE / (strict + ".log")).stat().st_size == 0
    script = (HERE / (strict + ".sh")).read_text()
    assert "lean4---v4.34.1/bin/lean -Dlinter.all=true " in script
    assert str(HERE / (strict + ".source.lean")) in script
    assert (HERE / (strict + ".caps")).read_text().splitlines() == ["4294967296", "4294967296", "0"]
    canonical_metadata = json.loads((HERE / (canonical + ".json")).read_text())
    assert canonical_metadata["exit_code"] == 0
    log = (HERE / (canonical + ".log")).read_text()
    assert f"Build completed successfully ({jobs} jobs)." in log
    assert not any(token in log for token in ["warning:", "error:", "sorryAx"])
    assert (HERE / (canonical + ".caps")).read_text().splitlines() == ["4294967296", "4294967296", "0"]

flags = [
    "set_option linter.all true", "set_option pp.explicit true",
    "set_option pp.fullNames true", "set_option pp.proofs true",
    "set_option pp.universes true", "set_option pp.deepTerms true",
    "set_option pp.proofs.threshold 254", "set_option pp.maxSteps 10000000",
]
public = integration = 0
for group in json.loads((HERE / "normalized-comparison-selected.json").read_text()):
    stem = group["stem"]
    source = (HERE / (stem + ".source.lean")).read_text()
    log = (HERE / (stem + ".log")).read_text()
    metadata = json.loads((HERE / (stem + ".json")).read_text())
    assert metadata["exit_code"] == 0
    assert all(flag in source for flag in flags)
    assert not any(token in log for token in ["warning:", "error:", "sorryAx", "⋯", "…", "...", "truncated"])
    assert (HERE / (stem + ".caps")).read_text().splitlines() == ["4294967296", "4294967296", "0"]
    reports = re.findall(r"depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms", log)
    assert len(reports) == group["pairs"], (stem, len(reports))
    for record in reports:
        names = [re.sub(r"\.\{[^}]*\}", "", name.strip()) for name in record.split(",") if name.strip()]
        assert set(names) <= {"propext", "Classical.choice", "Quot.sound"}, (stem, names)
    for name in group["names"]:
        local = name.rsplit(".", 1)[-1]
        assert "#check @" + name in source or "#check @" + local + "\n" in source
        assert "#print axioms " + name in source or "#print axioms " + local + "\n" in source
        assert name in log
        if group["kind"] == "public":
            assert "#print " + name + "\n" in source
    if group["kind"] == "public":
        public += group["pairs"]
    else:
        integration += group["pairs"]
assert public == manifest["public_pairs"] == 24
assert integration == manifest["integration_pairs"] == 2
assert len(json.loads((HERE / "normalized-comparison-selected.json").read_text())) == manifest["groups"] == 3
print(f"PASS: {len(manifest['files'])} pinned files; 24 full public pairs; 2 constructed integration pairs; actual 4 GiB limits")
