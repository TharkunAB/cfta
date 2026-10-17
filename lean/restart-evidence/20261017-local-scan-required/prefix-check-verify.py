#!/usr/bin/env python3
"""Verify the independent preparation kernels without changing files."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / "prefix-check-manifest.json").read_text())
for entry in manifest["entries"]:
    data = (ROOT / entry["path"]).read_bytes()
    assert len(data) == entry["bytes"], entry["path"]
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]

source = ROOT / "lean/MicroCFTA/SourceCurrentScanRequiredNumeric.lean"
assert hashlib.sha256(source.read_bytes()).hexdigest() == (
    "24534bc63167c1ef51074234e81e3a2193f04eac1799726f6bbe7a749759c916"
)
assert source.read_bytes() == (HERE / "scan-required-numeric-direct-4.source.lean").read_bytes()
assert (HERE / "scan-required-numeric-direct-4.log").stat().st_size == 0
assert "Build completed successfully (1716 jobs)." in (
    HERE / "scan-required-numeric-canonical-1.log"
).read_text()

kernel = (HERE / "prefix-check-kernels.lean").read_text()
assert kernel == (HERE / "prefix-check-kernels-3.source.lean").read_text()
strict = (HERE / "prefix-check-strict-1.source.lean").read_text()
assert strict == kernel[:kernel.index("\n#print axioms")]
assert (HERE / "prefix-check-strict-1.log").stat().st_size == 0
for stem in ["prefix-check-kernels-3", "prefix-check-strict-1"]:
    metadata = json.loads((HERE / (stem + ".json")).read_text())
    assert metadata["exit"] == 0
    assert metadata["command"][-1] == str(HERE / (stem + ".source.lean"))
    assert metadata["command"][1] == "-Dlinter.all=true"

log = (HERE / "prefix-check-kernels-3.log").read_text()
assert not re.search(r"\bsorryAx\b|: (?:error|warning)(?:\(|:)", log)
declarations = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log, re.S)
assert len(declarations) == 2
assert {name for name, _ in declarations} == {
    "MicroCFTA.PrefixCheckKernels.constructed_kept_prefix",
    "MicroCFTA.PrefixCheckKernels.constructed_empty_prefix",
}
for name, axioms in declarations:
    axes = re.sub(r"\.\{[^}]*\}", "", axioms)
    assert {axis.strip() for axis in axes.split(",") if axis.strip()} <= {
        "propext", "Classical.choice", "Quot.sound"
    }
    assert f"#check @{name}" in kernel
    assert f"#print {name}" in kernel
    assert re.search(re.escape(name) + r"(?:\.\{[^}]*\})?\s*:", log), name
print(f"PASS: {len(manifest['entries'])} frozen entries; 2 constructed preparation pairs")
