"""Verify cap-free initial native query Frame resources and its constructed integration."""

import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[3]
p = Path(__file__).resolve().parent
m = json.loads((p / "query-frame-manifest.json").read_text())
assert len(m["entries"]) == m["entry_count"]
for item in m["entries"]:
    assert hashlib.sha256((root / item["path"]).read_bytes()).hexdigest() == item["sha256"], item
module = root / "lean/MicroCFTA/SourceCurrentGeneratedQueryFrameResources.lean"
assert (p / "query-frame-direct-1.source.lean").read_bytes() == module.read_bytes()
assert (p / "query-frame-direct-1.log").stat().st_size == 0
assert "Build completed successfully (1406 jobs)" in (p / "query-frame-canonical-1.log").read_text()
for prefix, pairs in [("query-frame-public-1", 2), ("query-frame-kernels-2", 1)]:
    source = (p / f"{prefix}.source.lean").read_text()
    log = (p / f"{prefix}.log").read_text()
    assert not re.search(r"error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|\.\.\.", log)
    assert len(re.findall(r"^#check @", source, re.M)) == pairs
    assert len(re.findall(r"^#print axioms ", source, re.M)) == pairs
    blocks = re.findall(r"depends on axioms: \[([^\]]*)\]", log, re.S)
    assert len(blocks) + log.count("does not depend on any axioms") == pairs
    for block in blocks:
        assert {re.sub(r"\.\{[^}]+\}", "", n.strip()) for n in block.split(",") if n.strip()} <= {"propext", "Classical.choice", "Quot.sound"}
print(f"PASS: {m['entry_count']} hashes; public2 and constructed uncapped closed Mu query1; strict empty; canonical1406")
