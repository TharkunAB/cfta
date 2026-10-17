"""Verify immutable secondary gate resource evidence."""
import hashlib
import json
from pathlib import Path
import re

p = Path(__file__).resolve().parent
root = p.parents[2]
m = json.loads((p / "secondary-manifest.json").read_text())
assert len(m["entries"]) == m["entry_count"]
for item in m["entries"]:
    assert hashlib.sha256((root / item["path"]).read_bytes()).hexdigest() == item["sha256"], item
production = root / "lean/MicroCFTA/SourceCurrentSecondaryGateResources.lean"
assert production.read_bytes() == (p / "secondary-direct-2.source.lean").read_bytes()
assert (p / "secondary-direct-2.log").stat().st_size == 0
assert "Build completed successfully (1260 jobs)" in (p / "secondary-canonical-1.log").read_text()
for name, pairs in [("secondary-public-1", 4), ("secondary-kernels-4", 2)]:
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
print(f"PASS: {m['entry_count']} hashes; public4 + constructed integrations2; strict empty; canonical1260")
