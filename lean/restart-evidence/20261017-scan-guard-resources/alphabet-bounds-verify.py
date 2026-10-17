"""Verify the fixed-alphabet conjunction producer and its initial integrations."""
import hashlib
import json
from pathlib import Path
import re

p = Path(__file__).resolve().parent
root = p.parents[2]
m = json.loads((p / "alphabet-bounds-manifest.json").read_text())
assert len(m["entries"]) == m["entry_count"]
for item in m["entries"]:
    assert hashlib.sha256((root / item["path"]).read_bytes()).hexdigest() == item["sha256"], item
production = (root / "lean/MicroCFTA/SourceCurrentConjunctionAlphabetBounds.lean").read_bytes()
assert production == (p / "alphabet-bounds-direct-2.source.lean").read_bytes()
assert (p / "alphabet-bounds-direct-2.log").stat().st_size == 0
assert "Build completed successfully (1542 jobs)" in (p / "alphabet-bounds-canonical-1.log").read_text()
for name, pairs in [("alphabet-bounds-public-1", 10), ("alphabet-bounds-kernels-3", 2)]:
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
for failed in ["alphabet-bounds-direct-1", "alphabet-bounds-kernels-1", "alphabet-bounds-kernels-2"]:
    assert re.search(r"error(?:\(|:)", (p / (failed + ".log")).read_text())
kernel = (p / "alphabet-bounds-kernels-3.source.lean").read_text()
for fragment in ["private def alphabet : List Guard := [annotation, SourceEqualityConstraintConstructors.top]", "∀ depth, ¬Cap depth value", "Frame.initial", "InternedValueMassHeap.initial", "SourceCurrentConjunctionAlphabetBounds.caller_complete", "bounded inputs known", "post.trans post2", "saved value.referenceOf = some (value, answer)"]:
    assert fragment in kernel, fragment
assert kernel.count("SourceCurrentConjunctionAlphabetBounds.caller_complete") == 3
assert "sorry" not in production.decode()
assert not re.search(r"set_option linter[^\n]* false", production.decode())
print(f"PASS: {m['entry_count']} hashes; public10 + initial cold/warm kernels2; strict empty; canonical1542")
