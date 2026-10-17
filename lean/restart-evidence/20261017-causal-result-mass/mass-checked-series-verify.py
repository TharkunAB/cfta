"""Verify the final independent checked optional-series evidence."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

production = root / "lean/MicroCFTA/SourceCurrentAllocatedRecursiveMassCheckedSeries.lean"
expected = "a67ba3a804478833ade6f8e4948d6b6a7e9c843e41db95819e57e7bade3dc2fd"
assert digest(production) == expected
assert digest(evidence / "mass-checked-series-reviewed.source.lean") == expected
assert digest(evidence / "mass-checked-series-direct-3.source.lean") == expected
assert (evidence / "mass-checked-series-direct-3.log").read_bytes() == b""
names = re.findall(r"^(?:def|theorem) ([^ \(]+)", production.read_text(), re.M)
assert names == ["code", "replaceHeap", "code_fields", "same_tables", "trace", "complete"]
allowed = {"propext", "Classical.choice", "Quot.sound"}
for kind, attempt, count in [("public", 2, 6), ("kernels", 5, 2)]:
    source = evidence / f"mass-checked-series-{kind}.lean"
    assert source.read_bytes() == (evidence / f"mass-checked-series-{kind}-{attempt}.source.lean").read_bytes()
    text = source.read_text()
    log = (evidence / f"mass-checked-series-{kind}-{attempt}.log").read_text()
    assert not re.search(r"error:|warning:|sorryAx|truncated|⋯|\.\.\.", log)
    assert len(re.findall(r"^#print axioms ", text, re.M)) == count
    assert len(re.findall(r"^#check @", text, re.M)) == count
    blocks = re.findall(r"depends on axioms: \[([^\]]*)\]", log, re.S)
    none = re.findall(r"does not depend on any axioms", log)
    assert len(blocks) + len(none) == count
    axioms = {re.sub(r"\.\{[^}]+\}", "", n.strip()) for block in blocks for n in block.split(",") if n.strip()}
    assert axioms <= allowed, axioms
    for setting in ["linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.universes true", "pp.deepTerms true"]:
        assert "set_option " + setting in text
    limit = re.search(r"set_option pp.maxSteps (\d+)", text)
    assert limit and int(limit.group(1)) >= 1000000
    print(kind, count, "pairs clean", sorted(axioms))
canonical = (evidence / "mass-checked-series-final-canonical-audit.log").read_text()
assert "Build completed successfully (2864 jobs)." in canonical
assert "Checked axiom dependencies of 63784 MicroCFTA theorems." in canonical
assert "Built MicroCFTA.SourceCurrentAllocatedRecursiveMassCheckedSeries" in canonical
assert not re.search(r"error:|sorryAx", canonical)
warnings = re.findall(r"^warning: (.*)$", canonical, re.M)
assert len(warnings) == 1 and "InternedFreshOrdinaryClosedCompletion.lean:24" in warnings[0]
manifest = evidence / "mass-checked-series-manifest.json"
if manifest.exists():
    document = json.loads(manifest.read_text())
    assert len(document["files"]) == document["file_count"]
    for item in document["files"]:
        path = root / item["path"]
        assert digest(path) == item["sha256"], item["path"]
        assert path.stat().st_size == item["bytes"], item["path"]
    print("all", document["file_count"], "frozen manifest entries match")
print("PASS: exact corrected source, six public pairs, two initial-only checked/source integration kernels, final canonical Audit")
