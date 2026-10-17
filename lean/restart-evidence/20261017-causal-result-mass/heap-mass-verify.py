"""Verify causal heap mass source and imported proof evidence."""
from pathlib import Path
import hashlib
import json
import re
root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
allowed = {"propext", "Classical.choice", "Quot.sound"}
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
expected = {
    "InternedValueMassHeap": "7505bb38a993efb0bdb48cd772a2ace9a9054c33f1e1050acbf1bc8a51242c19",
    "InternedValueMassConstructors": "3051a422e70b9d49fb8c3b38a9af326885ed87ec2400c803647b0c2b7a1dfba5",
}
for name, value in expected.items():
    assert digest(root / f"lean/MicroCFTA/{name}.lean") == value
for name in ["heap-mass-direct-3.log", "mass-constructors-direct-3.log"]:
    assert (evidence / name).read_bytes() == b""
for label, count, attempt in [("public", 27, 1), ("kernels", 2, 2)]:
    source = (evidence / f"heap-mass-{label}.lean").read_text()
    log = (evidence / f"heap-mass-{label}-{attempt}.log").read_text()
    assert not re.search(r"error:|warning:|sorryAx|truncated|⋯|\.\.\.", log), label
    assert len(re.findall(r"^#print axioms ", source, re.M)) == count
    assert len(re.findall(r"^#check @", source, re.M)) == count
    blocks = re.findall(r"depends on axioms: \[([^\]]*)\]", log, re.S)
    none = re.findall(r"does not depend on any axioms", log)
    assert len(blocks) + len(none) == count
    axioms = {re.sub(r"\.\{[^}]+\}", "", n.strip()) for b in blocks for n in b.split(",") if n.strip()}
    assert axioms <= allowed, (label, axioms)
    for setting in ["linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.universes true", "pp.deepTerms true"]:
        assert "set_option " + setting in source
    steps = re.search(r"set_option pp.maxSteps (\d+)", source)
    assert steps and int(steps.group(1)) >= 1000000
    print(label, count, "pairs clean", sorted(axioms))
for name, jobs in [("heap-mass-canonical.log", 1176), ("mass-constructors-canonical.log", 1179)]:
    log = (evidence / name).read_text()
    assert f"Build completed successfully ({jobs} jobs)." in log
    assert not re.search(r"error:|sorryAx", log)
manifest = evidence / "heap-mass-manifest.json"
if manifest.exists():
    for item in json.loads(manifest.read_text())["files"]:
        path = root / item["path"]
        assert digest(path) == item["sha256"], item["path"]
        assert path.stat().st_size == item["bytes"], item["path"]
    print("all frozen manifest entries match")
print("PASS: causal heap mass, initial producer, actual constructors, public and integration evidence")
