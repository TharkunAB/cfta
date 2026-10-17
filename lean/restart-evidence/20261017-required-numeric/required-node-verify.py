#!/usr/bin/env python3
"""Verify immutable supported required-nodeer evidence without a build."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / "required-node-manifest.json").read_text())
assert len(manifest["entries"]) == manifest["entry_count"]
seen = set()
for entry in manifest["entries"]:
    assert entry["path"] not in seen, entry["path"]
    seen.add(entry["path"])
    data = (ROOT / entry["path"]).read_bytes()
    assert len(data) == entry["bytes"], entry["path"]
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]
for production in manifest["production"]:
    assert (HERE / production["strict_log"]).read_bytes() == b""
    assert (ROOT / production["path"]).read_bytes() == (HERE / production["strict_snapshot"]).read_bytes()
    canonical = (HERE / production["canonical_log"]).read_text()
    assert f"Build completed successfully ({production['canonical_jobs']} jobs)." in canonical
    assert "Built MicroCFTA." + Path(production["path"]).stem in canonical
for check in manifest["checks"]:
    source = (HERE / check["source"]).read_text()
    log = (HERE / check["log"]).read_text()
    assert (HERE / check["source"]).read_bytes() == (HERE / check["snapshot"]).read_bytes()
    assert not re.search(r"error(?:\(|:)|warning:|sorryAx|truncated|maximum.*(?:depth|steps)", log), check["log"]
    pairs = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.M | re.S)
    pairs += [(name, "") for name in re.findall(r"^'([^']+)' does not depend on any axioms$", log, re.M)]
    assert len(pairs) == check["pairs"], (check["log"], len(pairs))
    for directive in ["#print axioms ", "#check @"]:
        assert len(re.findall("^" + re.escape(directive), source, re.M)) == check["pairs"]
    for name, axioms in pairs:
        for directive in ["#print axioms ", "#check @", "#print "]:
            assert directive + name + "\n" in source, name
        assert re.search(r"^@?" + re.escape(name) + r"\s*:", log, re.M), name
        names = [re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in axioms.split(",") if item.strip()]
        assert set(names) <= {"propext", "Classical.choice", "Quot.sound"}, (name, names)
    for setting in ["pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000", "linter.all true"]:
        assert "set_option " + setting in source, setting
public = (HERE / "required-node-public.lean").read_text()
for production in manifest["production"]:
    source = (ROOT / production["path"]).read_text()
    for name in re.findall(r"^theorem\s+(\w+)", source, re.M):
        full = "MicroCFTA." + Path(production["path"]).stem + "." + name
        assert "#check @" + full + "\n" in public, full
attempts = json.loads((HERE / "required-node-attempts.json").read_text())
for attempt in attempts["attempts"]:
    assert (HERE / attempt["log"]).exists()
    if "snapshot" in attempt:
        assert (HERE / attempt["snapshot"]).exists()
print("PASS:", manifest["entry_count"], "hashes;", sum(c["pairs"] for c in manifest["checks"]), "complete pairs; current diagnostics 0")
