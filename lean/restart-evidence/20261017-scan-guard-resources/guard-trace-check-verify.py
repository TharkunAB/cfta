"""Verify independent native guard step, trace, and initial query evidence."""
import hashlib
import json
from pathlib import Path
import re

p = Path(__file__).resolve().parent
root = p.parents[2]
m = json.loads((p / "guard-trace-check-manifest.json").read_text())
v = json.loads((p / "guard-trace-check-validation.json").read_text())
assert len(m["entries"]) == m["entry_count"]
for item in m["entries"]:
    assert hashlib.sha256((root / item["path"]).read_bytes()).hexdigest() == item["sha256"], item
for item in v["production"]:
    assert (root / item["source"]).read_bytes() == (p / item["strict_source"]).read_bytes()
    assert (p / item["strict_log"]).stat().st_size == 0
    assert f"Build completed successfully ({item['canonical_jobs']} jobs)" in (p / item["canonical_log"]).read_text()
for name, pairs in [("guard-trace-check-public-1", 11), ("guard-trace-check-kernels-1", 2)]:
    source = (p / (name + ".source.lean")).read_text()
    log = (p / (name + ".log")).read_text()
    assert not re.search(r"error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|\.\.\.", log)
    assert len(re.findall(r"^#check @", source, re.M)) == pairs
    assert len(re.findall(r"^#print axioms ", source, re.M)) == pairs
    for option in ["pp.explicit", "pp.fullNames", "pp.proofs", "pp.universes", "pp.deepTerms"]:
        assert "set_option " + option + " true" in source
    assert "set_option pp.maxSteps 10000000" in source
    blocks = re.findall(r"depends on axioms: \[([^\]]*)\]", log, re.S)
    assert len(blocks) + log.count("does not depend on any axioms") == pairs
    for block in blocks:
        axioms = {re.sub(r"\.\{[^}]+\}", "", n.strip()) for n in block.split(",") if n.strip()}
        assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, axioms
kernel = (p / "guard-trace-check-kernels-1.source.lean").read_text()
for fragment in ["left ≠ right", "∀ depth, ¬Cap depth left", "private def alphabet : List Guard := [annotation]", "SourceEqualityAnnotationConstruction.build", "Frame.initial", "exists_room", "first.frame", "first.fits", "first.query.globals", "known EndpointMemoGateTrace.empty"]:
    assert fragment in kernel, fragment
assert kernel.count("SourceCurrentGeneratedQueryGuardResources.complete") == 3
print(f"PASS: {m['entry_count']} hashes; public11 + own initial recursive-query kernels2; all root strict empty")
