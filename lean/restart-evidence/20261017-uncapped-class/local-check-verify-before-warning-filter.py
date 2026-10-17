#!/usr/bin/env python3
"""Verify the frozen independent Local completion evidence without writes."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / "local-check-manifest.json").read_text())
for entry in manifest["entries"]:
    data = (ROOT / entry["path"]).read_bytes()
    assert len(data) == entry["bytes"], entry["path"]
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]

for module, strict, canonical, jobs in [
    ("SourceCurrentLocalForecast", "local-forecast-direct-1", "local-forecast-canonical-1", 1662),
    ("SourceCurrentLocalNumeric", "local-numeric-direct-3", "local-numeric-canonical-1", 1744),
]:
    source = ROOT / "lean/MicroCFTA" / (module + ".lean")
    assert source.read_bytes() == (HERE / (strict + ".source.lean")).read_bytes(), module
    assert (HERE / (strict + ".log")).stat().st_size == 0, strict
    log = (HERE / (canonical + ".log")).read_text()
    assert f"Build completed successfully ({jobs} jobs)." in log, canonical
    warnings = [line for line in log.splitlines() if "warning:" in line]
    assert all(line.startswith("warning: MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5:") for line in warnings), warnings

for stem, count in [("local-check-public-1", 12), ("local-check-kernels-6", 3)]:
    metadata = json.loads((HERE / (stem + ".json")).read_text())
    assert metadata["exit"] == 0, stem
    assert metadata["command"][-1] == str(HERE / (stem + ".source.lean")), stem
    assert metadata["command"][1] == "-Dlinter.all=true", stem
    source = (HERE / (stem + ".source.lean")).read_text()
    log = (HERE / (stem + ".log")).read_text()
    assert not re.search(r"\bsorryAx\b|: (?:error|warning)(?:\(|:)", log), stem
    declarations = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log, re.S)
    declarations += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", log)]
    assert len(declarations) == count, (stem, len(declarations))
    assert len(set(name for name, _ in declarations)) == count, stem
    for name, axioms in declarations:
        axes = re.sub(r"\.\{[^}]*\}", "", axioms)
        assert {x.strip() for x in axes.split(",") if x.strip()} <= {
            "propext", "Classical.choice", "Quot.sound"
        }, (name, axioms)
        assert f"#check @{name}" in source, name
        assert f"#print {name}" in source, name
        assert re.search(re.escape(name) + r"(?:\.\{[^}]*\})?\s*:", log), name

kernel = (HERE / "local-check-kernels.lean").read_text()
assert kernel == (HERE / "local-check-kernels-6.source.lean").read_text()
strict = "local-check-kernel-strict-1"
assert kernel[:kernel.index("\n#print axioms")] == (HERE / (strict + ".source.lean")).read_text()
assert (HERE / (strict + ".log")).stat().st_size == 0
metadata = json.loads((HERE / (strict + ".json")).read_text())
assert metadata["exit"] == 0
assert metadata["command"][-1] == str(HERE / (strict + ".source.lean"))
for number in range(1, 6):
    stem = f"local-check-kernels-{number}"
    metadata = json.loads((HERE / (stem + ".json")).read_text())
    assert metadata["exit"] != 0, stem
    assert metadata["command"][-1] == str(HERE / (stem + ".source.lean")), stem
    assert (HERE / (stem + ".log")).stat().st_size > 0, stem
print(f"PASS: {len(manifest['entries'])} frozen entries; 12 public + 3 kernel pairs")
