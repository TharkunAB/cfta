"""Verify the frozen initial class fold without rebuilding."""

import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
manifest = json.loads((evidence / "class-pass-manifest.json").read_text())
assert manifest["entry_count"] == len(manifest["entries"])
for entry in manifest["entries"]:
    data = (root / entry["path"]).read_bytes()
    assert len(data) == entry["bytes"], entry["path"]
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]
assert (root / "lean/MicroCFTA/SourceCurrentConstrainedCapClassPassNumeric.lean").read_bytes() == (evidence / "class-pass-numeric-direct-2.source.lean").read_bytes()
assert (evidence / "class-pass-numeric-direct-2.log").read_bytes() == b""
assert "Build completed successfully (1565 jobs)." in (evidence / "class-pass-numeric-canonical-1.log").read_text()
total = 0
for source_name, log_name, pairs in [
    ("class-pass-public-1.source.lean", "class-pass-public-1.log", 2),
    ("class-pass-empty-kernels-1.source.lean", "class-pass-empty-kernels-1.log", 1),
]:
    source = (evidence / source_name).read_text()
    log = (evidence / log_name).read_text()
    assert not re.search(r"error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|\.\.\.", log), log_name
    names = re.findall(r"^#print axioms (\S+)", source, re.M)
    assert len(names) == len(re.findall(r"^#check @", source, re.M)) == pairs
    blocks = re.findall(r"depends on axioms: \[([^\]]*)\]", log, re.S)
    assert len(blocks) + log.count("does not depend on any axioms") == pairs
    for name in names:
        assert name in log and "#print " + name in source, name
    for block in blocks:
        axioms = {re.sub(r"\.\{[^}]+\}", "", name.strip()) for name in block.split(",") if name.strip()}
        assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, axioms
    for setting in ["linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]:
        assert "set_option " + setting in source, setting
    total += pairs
print(f"PASS: {len(manifest['entries'])} hashes; {total} full pairs; strict clean; canonical pass; standard axioms")
