"""Verify the initial selected Required numeric completion evidence."""

import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
manifest = json.loads((evidence / "initial-manifest.json").read_text())
assert len(manifest["entries"]) == manifest["entry_count"]
for item in manifest["entries"]:
    assert hashlib.sha256((root / item["path"]).read_bytes()).hexdigest() == item["sha256"], item
module = root / "lean/MicroCFTA/SourceCurrentConstrainedCapRequiredInitialNumeric.lean"
assert (evidence / "initial-direct-2.source.lean").read_bytes() == module.read_bytes()
assert (evidence / "initial-direct-2.log").stat().st_size == 0
assert "Build completed successfully (1563 jobs)" in (evidence / "initial-canonical-1.log").read_text()
for prefix, pairs in [("initial-public-1", 7), ("initial-contract-1", 1)]:
    source = (evidence / f"{prefix}.source.lean").read_text()
    log = (evidence / f"{prefix}.log").read_text()
    assert not re.search(r"error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|\.\.\.", log)
    assert len(re.findall(r"^#check @", source, re.M)) == pairs
    assert len(re.findall(r"^#print axioms ", source, re.M)) == pairs
    blocks = re.findall(r"depends on axioms: \[([^\]]*)\]", log, re.S)
    assert len(blocks) + log.count("does not depend on any axioms") == pairs
    for block in blocks:
        assert {re.sub(r"\.\{[^}]+\}", "", name.strip()) for name in block.split(",") if name.strip()} <= {"propext", "Classical.choice", "Quot.sound"}
print(f"PASS: {manifest['entry_count']} hashes; 7 public pairs; 1 initial contract; strict clean; canonical1563")
