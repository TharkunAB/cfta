"""Verify independent compiled-emitter input evidence."""
from pathlib import Path
import hashlib
import json
import re
root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

expected = "81b035d24ecd56417cf9d8ee955b57cb770ba70fda4140fffa643c6270253705"
production = root / "lean/MicroCFTA/SourceRecursiveIntersectionCompileMassInputs.lean"
assert digest(production) == expected
assert digest(evidence / "compile-inputs-review-reviewed.source.lean") == expected
assert digest(evidence / "compile-inputs-direct-2.source.lean") == expected
assert (evidence / "compile-inputs-direct-2.log").read_bytes() == b""
assert re.findall(r"^theorem ([^ \(]+)", production.read_text(), re.M) == ["rows", "le_square", "union"]
allowed = {"propext", "Classical.choice", "Quot.sound"}
for kind, attempt, count in [("public", 1, 3), ("kernels", 2, 2)]:
    source = evidence / f"compile-inputs-review-{kind}.lean"
    assert source.read_bytes() == (evidence / f"compile-inputs-review-{kind}-{attempt}.source.lean").read_bytes()
    text = source.read_text()
    log = (evidence / f"compile-inputs-review-{kind}-{attempt}.log").read_text()
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
canonical = (evidence / "compile-inputs-review-canonical.log").read_text()
assert "Build completed successfully (1185 jobs)." in canonical
assert "Built MicroCFTA.SourceRecursiveIntersectionCompileMassInputs" in canonical
assert not re.search(r"error:|sorryAx", canonical)
warnings = re.findall(r"^warning: (.*)$", canonical, re.M)
assert len(warnings) == 1 and "InternedFreshOrdinaryClosedCompletion.lean:24" in warnings[0]
manifest = evidence / "compile-inputs-review-manifest.json"
if manifest.exists():
    document = json.loads(manifest.read_text())
    assert len(document["files"]) == document["file_count"]
    for item in document["files"]:
        path = root / item["path"]
        assert digest(path) == item["sha256"], item["path"]
        assert path.stat().st_size == item["bytes"], item["path"]
    print("all", document["file_count"], "frozen manifest entries match")
print("PASS: exact source, strict/canonical target, three public pairs, two constructed row/union prefix certificate kernels")
