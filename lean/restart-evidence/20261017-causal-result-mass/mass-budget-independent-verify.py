"""Verify independent optional mass-budget evidence."""
from pathlib import Path
import hashlib
import json
import re
root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
assert digest(root / "lean/MicroCFTA/SourceCurrentAllocatedRecursiveMassBudget.lean") == "c4b8def6117851f5b431555fa8982b49078d9c001d7625b391cf31ef8b0537d5"
assert (evidence / "mass-budget-direct-1.log").read_bytes() == b""
allowed = {"propext", "Classical.choice", "Quot.sound"}
for label, count in [("public", 9), ("kernels", 2)]:
    source = (evidence / f"mass-budget-{label}.lean").read_text()
    log = (evidence / f"mass-budget-{label}-1.log").read_text()
    assert not re.search(r"error:|warning:|sorryAx|truncated|⋯|\.\.\.", log)
    assert len(re.findall(r"^#print axioms ", source, re.M)) == count
    assert len(re.findall(r"^#check @", source, re.M)) == count
    blocks = re.findall(r"depends on axioms: \[([^\]]*)\]", log, re.S)
    none = re.findall(r"does not depend on any axioms", log)
    assert len(blocks) + len(none) == count
    axioms = {re.sub(r"\.\{[^}]+\}", "", n.strip()) for block in blocks for n in block.split(",") if n.strip()}
    assert axioms <= allowed
    for setting in ["linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.universes true", "pp.deepTerms true"]:
        assert "set_option " + setting in source
    limit = re.search(r"set_option pp.maxSteps (\d+)", source)
    assert limit and int(limit.group(1)) >= 1000000
    print(label, count, "pairs clean", sorted(axioms))
log = (evidence / "mass-budget-independent-canonical.log").read_text()
assert "Build completed successfully (1187 jobs)." in log
assert not re.search(r"error:|sorryAx", log)
manifest = evidence / "mass-budget-independent-manifest.json"
if manifest.exists():
    for item in json.loads(manifest.read_text())["files"]:
        path = root / item["path"]
        assert digest(path) == item["sha256"], item["path"]
        assert path.stat().st_size == item["bytes"], item["path"]
    print("all frozen manifest entries match")
print("PASS: exact source, canonical target, nine public and two constructed numeric optional kernels")
