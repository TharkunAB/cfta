"""Verify the frozen native guard occurrence growth component."""
from pathlib import Path
import hashlib
import json
import re

here = Path(__file__).resolve().parent
root = here.parents[2]
manifest = json.loads((here / "guard-growth-manifest.json").read_text())
assert len(manifest["entries"]) == manifest["entry_count"]
for entry in manifest["entries"]:
    raw = (root / entry["path"]).read_bytes()
    assert len(raw) == entry["bytes"], entry["path"]
    assert hashlib.sha256(raw).hexdigest() == entry["sha256"], entry["path"]
source = (root / "lean/MicroCFTA/SourceCurrentNativeGuardOccurrenceGrowth.lean").read_bytes()
assert source == (here / "guard-growth-direct-2.source.lean").read_bytes()
assert hashlib.sha256(source).hexdigest() == "66e23d16a59642daca467f19c4dbacf6d9dc3d38386fab9f02a00e07b333b09c"
assert (here / "guard-growth-direct-2.log").stat().st_size == 0
assert not re.search(r"\b(sorry|axiom)\b", source.decode())
for term in ["SourceRecursiveIntersectionNative.execute", "buildMany programs [] empty", "depth first = 1", "depth second = 1", "depth output = 2", "InternedNestedFacts.Facts initial", "first.free = []", "second.free = []"]:
    assert term in source.decode(), term
for stem in ["guard-growth-direct-2", "guard-growth-canonical-1", "guard-growth-public-1"]:
    caps = json.loads((here / f"{stem}.caps.json").read_text())
    assert caps == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
    assert (here / f"{stem}.peaks").read_text().strip().endswith(" 0")
canonical = (here / "guard-growth-canonical-1.log").read_text()
assert "Build completed successfully (1002 jobs)." in canonical
probe = (here / "guard-growth-public-1.source.lean").read_text()
log = (here / "guard-growth-public-1.log").read_text()
assert not re.search(r"error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|\.\.\.", log)
assert len(re.findall(r"^#check @", probe, re.M)) == 4
assert len(re.findall(r"^#print axioms ", probe, re.M)) == 4
assert len(re.findall(r"^#print (?!axioms )", probe, re.M)) == 4
for option in ["pp.explicit", "pp.fullNames", "pp.proofs", "pp.universes", "pp.deepTerms"]:
    assert f"set_option {option} true" in probe
assert "set_option pp.proofs.threshold 254" in probe
assert "set_option pp.maxSteps 10000000" in probe
blocks = re.findall(r"depends on axioms: \[([^\]]*)\]", log, re.S)
assert len(blocks) + log.count("does not depend on any axioms") == 4
for block in blocks:
    axioms = {re.sub(r"\.\{[^}]+\}", "", name.strip()) for name in block.split(",") if name.strip()}
    assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, axioms
assert "error(lean.dependsOnNoncomputable)" in (here / "guard-product-2.log").read_text()
for number in [1, 3]:
    assert not re.search(r"error(?:\(|:)|warning(?:\(|:)|sorryAx", (here / f"guard-product-{number}.log").read_text())
assert manifest["public_pairs"] == 4
assert manifest["integration_pairs"] == 0
assert manifest["constructed_witnesses_within_public"] == 1
print(f"PASS: {manifest['entry_count']} hashes; strict2 empty; capped canonical1002; public4 full signatures/proofs; one own constructed witness counted within public; standard axioms")
