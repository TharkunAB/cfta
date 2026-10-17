#!/usr/bin/env python3
"""Verify the frozen edit frame component without rebuilding."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / "edit-frame-manifest.json").read_text())
assert len(manifest["entries"]) == manifest["entry_count"]
seen = set()
for entry in manifest["entries"]:
    assert entry["path"] not in seen, entry["path"]
    seen.add(entry["path"])
    data = (ROOT / entry["path"]).read_bytes()
    assert len(data) == entry["bytes"], entry["path"]
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]
assert (ROOT / manifest["strict_log"]).read_bytes() == b""
assert (ROOT / manifest["source"]).read_bytes() == (HERE / "edit-frame-direct-3.source.lean").read_bytes()
canonical = (ROOT / manifest["canonical_log"]).read_text()
assert "Build completed successfully (1526 jobs)." in canonical
assert "Built MicroCFTA.SourceCurrentConstrainedCapEditFrame" in canonical
for check in manifest["checks"]:
    source = (ROOT / check["source"]).read_text()
    log = (ROOT / check["log"]).read_text()
    assert not re.search(r"error(?:\(|:)|warning:|sorryAx|truncated|maximum.*(?:depth|steps)", log), check["log"]
    pairs = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.M | re.S)
    pairs += [(name, "") for name in re.findall(r"^'([^']+)' does not depend on any axioms$", log, re.M)]
    assert len(pairs) == check["pairs"], (check["log"], len(pairs))
    assert len(re.findall(r"^#print axioms ", source, re.M)) == check["pairs"]
    assert len(re.findall(r"^#check @", source, re.M)) == check["pairs"]
    for name, axioms in pairs:
        short = name.rsplit(".", 1)[-1]
        assert "#print axioms " + name in source or "#print axioms " + short in source
        assert "#check @" + name in source or "#check @" + short in source
        assert re.search(r"^@?" + re.escape(name) + r"\s*:", log, re.M), name
        names = [re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in axioms.split(",") if item.strip()]
        assert set(names) <= {"propext", "Classical.choice", "Quot.sound"}, (name, names)
    for setting in ["pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000", "linter.all true"]:
        assert "set_option " + setting in source, setting
    assert source.endswith("\n") and not source.endswith("\n\n")
assert (HERE / "edit-frame-kernels.lean").read_bytes() == (HERE / "edit-frame-kernels-1.source.lean").read_bytes()
print("PASS:", manifest["entry_count"], "hashes;", sum(c["pairs"] for c in manifest["checks"]), "complete pairs; diagnostics 0")
