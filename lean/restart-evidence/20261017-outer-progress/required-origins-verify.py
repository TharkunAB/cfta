#!/usr/bin/env python3
"""Verify the frozen Required guard-origin component without writing files."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / "required-origins-manifest.json").read_text())
for entry in manifest["entries"]:
    data = (ROOT / entry["path"]).read_bytes()
    assert len(data) == entry["bytes"], entry["path"]
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]
source = ROOT / "lean/MicroCFTA/SourceCurrentRequiredGuardOrigins.lean"
assert source.read_bytes() == (HERE / "required-origins-direct-3.source.lean").read_bytes()
assert (HERE / "required-origins-direct-3.log").stat().st_size == 0
for attempt in range(1, 4):
    stem = f"required-origins-direct-{attempt}"
    metadata = json.loads((HERE / (stem + ".json")).read_text())
    assert metadata["exit"] == (1 if attempt == 1 else 0), stem
    assert metadata["command"][-1] == str(HERE / (stem + ".source.lean")), stem
    assert metadata["command"][1] == "-Dlinter.all=true", stem
assert json.loads((HERE / "required-origins-canonical-1.json").read_text())["exit"] == 0
log = (HERE / "required-origins-canonical-1.log").read_text()
assert "Build completed successfully (1128 jobs)." in log
assert all(line.startswith("warning: MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5:")
           for line in log.splitlines() if line.startswith("warning:"))
for stem, count in [("required-origins-public-1", 6), ("required-origins-kernels-3", 2)]:
    metadata = json.loads((HERE / (stem + ".json")).read_text())
    assert metadata["exit"] == 0, stem
    assert metadata["command"][-1] == str(HERE / (stem + ".source.lean")), stem
    assert metadata["command"][1] == "-Dlinter.all=true", stem
    probe = (HERE / (stem + ".source.lean")).read_text()
    assert "set_option pp.proofs.threshold 254" in probe
    output = (HERE / (stem + ".log")).read_text()
    assert not re.search(r"⋯|…|\.{3}|truncat", output, re.I), stem
    assert not re.search(r"\bsorryAx\b|: (?:error|warning)(?:\(|:)", output), stem
    declarations = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output, re.S)
    declarations += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", output)]
    assert len(declarations) == count, (stem, len(declarations))
    assert len({name for name, _ in declarations}) == count, stem
    for name, axioms in declarations:
        axes = re.sub(r"\.\{[^}]*\}", "", axioms)
        assert {x.strip() for x in axes.split(",") if x.strip()} <= {
            "propext", "Classical.choice", "Quot.sound"
        }, (name, axioms)
        assert f"#print axioms {name}" in probe, name
        assert f"#check @{name}" in probe, name
        if stem == "required-origins-public-1":
            assert f"#print {name}" in probe, name
        else:
            assert f"#print {name}" not in probe, name
        assert re.search(re.escape(name) + r"(?:\.\{[^}]*\})?\s*:", output), name
kernel = (HERE / "required-origins-kernels.lean").read_text()
assert kernel == (HERE / "required-origins-kernels-3.source.lean").read_text()
strict = "required-origins-kernel-strict-1"
assert kernel[:kernel.index("\n#print axioms")] == (HERE / (strict + ".source.lean")).read_text()
assert (HERE / (strict + ".log")).stat().st_size == 0
metadata = json.loads((HERE / (strict + ".json")).read_text())
assert metadata["exit"] == 0
assert metadata["command"][-1] == str(HERE / (strict + ".source.lean"))
for attempt, expected in [(1, 1), (2, 0)]:
    stem = f"required-origins-kernels-{attempt}"
    assert json.loads((HERE / (stem + ".json")).read_text())["exit"] == expected
    assert (HERE / (stem + ".source.lean")).exists()
    assert (HERE / (stem + ".log")).exists()
print(f"PASS: {len(manifest['entries'])} frozen entries; 6 public + 2 constructed kernel pairs")
