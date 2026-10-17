#!/usr/bin/env python3
"""Verify the frozen uncapped editor component without writing files."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / "edit-uncapped-manifest.json").read_text())
for entry in manifest["entries"]:
    data = (ROOT / entry["path"]).read_bytes()
    assert len(data) == entry["bytes"], entry["path"]
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]

for module, prefix, jobs in [
    ("SourceCurrentEditFrame", "edit-frame", 1527),
    ("SourceCurrentEditScans", "edit-scans", 1542),
    ("SourceCurrentEditNumeric", "edit-node", 1550),
    ("SourceCurrentEditListNumeric", "edit-list", 1551),
]:
    source = ROOT / "lean/MicroCFTA" / (module + ".lean")
    snapshot = HERE / (prefix + "-direct-1.source.lean")
    assert source.read_bytes() == snapshot.read_bytes(), module
    assert (HERE / (prefix + "-direct-1.log")).stat().st_size == 0
    metadata = json.loads((HERE / (prefix + "-direct-1.json")).read_text())
    assert metadata["exit"] == 0
    assert metadata["command"][-1] == str(snapshot)
    assert metadata["command"][1] == "-Dlinter.all=true"
    assert json.loads((HERE / (prefix + "-canonical-1.json")).read_text())["exit"] == 0
    assert f"Build completed successfully ({jobs} jobs)." in (
        HERE / (prefix + "-canonical-1.log")
    ).read_text()

for stem, count in [("edit-uncapped-public-1", 22), ("edit-uncapped-kernels-2", 2)]:
    metadata = json.loads((HERE / (stem + ".json")).read_text())
    assert metadata["exit"] == 0
    source = (HERE / (stem + ".source.lean")).read_text()
    log = (HERE / (stem + ".log")).read_text()
    assert not re.search(r"\bsorryAx\b|: (?:error|warning)(?:\(|:)", log), stem
    declarations = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log, re.S)
    declarations += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", log)]
    assert len(declarations) == count, (stem, len(declarations))
    for name, axioms in declarations:
        axes = re.sub(r"\.\{[^}]*\}", "", axioms)
        assert {x.strip() for x in axes.split(",") if x.strip()} <= {
            "propext", "Classical.choice", "Quot.sound"
        }
        alias = name.replace("SourceCurrentConstrainedCapEditFrame.", "SourceCurrentEditFrame.")
        assert f"#check @{alias}" in source, alias
        assert f"#print {alias}" in source, alias
        assert re.search(re.escape(name) + r"(?:\.\{[^}]*\})?\s*:", log), name

kernel = (HERE / "edit-uncapped-kernels.lean").read_text()
assert kernel == (HERE / "edit-uncapped-kernels-2.source.lean").read_text()
assert kernel[:kernel.index("\n#print axioms")] == (
    HERE / "edit-uncapped-kernel-strict-1.source.lean"
).read_text()
assert (HERE / "edit-uncapped-kernel-strict-1.log").stat().st_size == 0
assert json.loads((HERE / "edit-uncapped-kernel-strict-1.json").read_text())["exit"] == 0
print(f"PASS: {len(manifest['entries'])} frozen entries; 22 public + 2 kernel pairs")
