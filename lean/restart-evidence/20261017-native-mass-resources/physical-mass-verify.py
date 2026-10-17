"""Verify current physical native payload mass evidence."""
from pathlib import Path
import hashlib
import json
import re
root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

expected = "f3c75004cc84f76ac9c086c35450ec91397fb446d5d039c5747e92454bd88ea4"
production = root / "lean/MicroCFTA/SourceCurrentAllocatedNativePhysicalMass.lean"
assert digest(production) == expected
for name in ["physical-mass-reviewed.source.lean", "physical-mass-direct-1.source.lean"]:
    assert digest(evidence / name) == expected
assert (evidence / "physical-mass-direct-1.log").read_bytes() == b""
names = re.findall(r"^(?:def|theorem) ([^ \(]+)", production.read_text(), re.M)
assert names == ["NodeMass", "EdgeMass", "node_cell", "edge_cell", "initial_cells", "read_bound", "edge_read_bound", "resident_children"]
allowed = {"propext", "Classical.choice", "Quot.sound"}
for kind, attempt, count in [("public", 1, 8), ("kernels", 4, 2)]:
    source = evidence / f"physical-mass-{kind}.lean"
    assert source.read_bytes() == (evidence / f"physical-mass-{kind}-{attempt}.source.lean").read_bytes()
    text = source.read_text()
    log = (evidence / f"physical-mass-{kind}-{attempt}.log").read_text()
    assert not re.search(r"error:|warning:|sorryAx|truncated|⋯|\.\.\.", log)
    assert len(re.findall(r"^#print axioms ", text, re.M)) == count
    assert len(re.findall(r"^#check @", text, re.M)) == count
    blocks = re.findall(r"depends on axioms: \[([^\]]*)\]", log, re.S)
    none = re.findall(r"does not depend on any axioms", log)
    assert len(blocks) + len(none) == count
    axioms = {re.sub(r"\.\{[^}]+\}", "", n.strip()) for block in blocks for n in block.split(",") if n.strip()}
    assert axioms <= allowed
    for setting in ["linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.universes true", "pp.deepTerms true"]:
        assert "set_option " + setting in text
    limit = re.search(r"set_option pp.maxSteps (\d+)", text)
    assert limit and int(limit.group(1)) >= 1000000
    print(kind, count, "pairs clean", sorted(axioms))
canonical = (evidence / "physical-mass-canonical.log").read_text()
assert "Build completed successfully (1177 jobs)." in canonical
assert "Built MicroCFTA.SourceCurrentAllocatedNativePhysicalMass" in canonical
assert not re.search(r"error:|sorryAx", canonical)
warnings = re.findall(r"^warning: (.*)$", canonical, re.M)
assert len(warnings) == 1 and "InternedFreshOrdinaryClosedCompletion.lean:24" in warnings[0]
manifest = evidence / "physical-mass-manifest.json"
if manifest.exists():
    document = json.loads(manifest.read_text())
    assert len(document["files"]) == document["file_count"]
    for item in document["files"]:
        path = root / item["path"]
        assert digest(path) == item["sha256"], item["path"]
        assert path.stat().st_size == item["bytes"], item["path"]
    print("all", document["file_count"], "frozen manifest entries match")
print("PASS: exact source, strict and canonical target, eight public pairs, two source-built populated/warm memo lifecycle kernels")
