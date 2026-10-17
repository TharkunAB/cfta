"""Verify the independent conjunction caller review and its initial integration."""
import hashlib
import json
from pathlib import Path
import re

p = Path(__file__).resolve().parent
root = p.parents[2]
m = json.loads((p / "memo-frame-check-manifest.json").read_text())
assert len(m["entries"]) == m["entry_count"]
for item in m["entries"]:
    assert hashlib.sha256((root / item["path"]).read_bytes()).hexdigest() == item["sha256"], item
assert (root / "lean/MicroCFTA/SourceCurrentConjunctionCallerNumeric.lean").read_bytes() == (p / "memo-frame-direct-1.source.lean").read_bytes()
assert (p / "memo-frame-direct-1.log").stat().st_size == 0
assert "Build completed successfully (1541 jobs)" in (p / "memo-frame-canonical-1.log").read_text()
for name, pairs in [("memo-frame-check-public-1", 3), ("memo-frame-check-kernels-1", 1)]:
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
kernel = (p / "memo-frame-check-kernels-1.source.lean").read_text()
for fragment in ["SourceCurrentConjunctionCallerNumeric.complete", "Frame.initial", "SourceCurrentAllocatedPartialInvariant.Context", "InternedValueMassHeap.initial", "∀ depth, ¬Cap depth value", "saved value.referenceOf = some (value, answer)", "Call 3 saved value after answer after saved"]:
    assert fragment in kernel, fragment
print(f"PASS: {m['entry_count']} hashes; public3 + own initial caller integration1; strict empty; canonical1541")
