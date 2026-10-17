"""Verify the frozen initial numeric edge-call component."""
from pathlib import Path
import hashlib
import json
import re
p = Path(__file__).resolve().parent
root = p.parents[2]
m = json.loads((p / "edge-call-manifest.json").read_text())
assert len(m["entries"]) == m["entry_count"]
for entry in m["entries"]:
    raw = (root / entry["path"]).read_bytes()
    assert len(raw) == entry["bytes"], entry["path"]
    assert hashlib.sha256(raw).hexdigest() == entry["sha256"], entry["path"]
source = (root / "lean/MicroCFTA/SourceCurrentEdgeCallNumeric.lean").read_bytes()
assert source == (p / "edge-call-direct-2.source.lean").read_bytes()
assert hashlib.sha256(source).hexdigest() == "c258734b1ea6b5a9f5250e6df6dae02ad2b90bf9e33dc304af17804a0415e8be"
assert (p / "edge-call-direct-2.log").stat().st_size == 0
assert "Build completed successfully (1772 jobs)." in (p / "edge-call-canonical-1.log").read_text()
assert "SourceCurrentAllocatedPartialSourceReads (EdgeCallReads)" in source.decode()
for stem, pairs in [("edge-call-public-1", 15), ("edge-call-kernels-4", 2)]:
    code = (p / (stem + ".source.lean")).read_text()
    log = (p / (stem + ".log")).read_text()
    assert not re.search(r"error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|\.\.\.", log)
    assert len(re.findall(r"^#check @", code, re.M)) == pairs
    assert len(re.findall(r"^#print axioms ", code, re.M)) == pairs
    for option in ["pp.explicit", "pp.fullNames", "pp.proofs", "pp.universes", "pp.deepTerms"]:
        assert "set_option " + option + " true" in code
    assert "set_option pp.proofs.threshold 254" in code
    assert "set_option pp.maxSteps 10000000" in code
    blocks = re.findall(r"depends on axioms: \[([^\]]*)\]", log, re.S)
    assert len(blocks) + log.count("does not depend on any axioms") == pairs
    for block in blocks:
        axioms = {re.sub(r"\.\{[^}]+\}", "", term.strip()) for term in block.split(",") if term.strip()}
        assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, axioms
for stem in ["edge-call-direct-1", "edge-call-kernels-1", "edge-call-kernels-3"]:
    assert "error:" in (p / (stem + ".log")).read_text()
assert (p / "edge-call-kernels-2.log").stat().st_size == 0
kernels = (p / "edge-call-kernels-4.source.lean").read_text()
for term in ["constructed_cold_warm", "constructed_busy_no_room", "closed_complete", "no_cap", "row_resident", "SourceCurrentEdgeCallNumeric.evaluated", "SourceCurrentEdgeCallNumeric.ready", "completed_table receipt.actual", "¬SourceCurrentAllocatedNativeResourceForecast.Room 0 profile"]:
    assert term in kernels, term
print(f"PASS: {m['entry_count']} hashes; strict2 empty; canonical1772; public15 + source-built integrations2")
