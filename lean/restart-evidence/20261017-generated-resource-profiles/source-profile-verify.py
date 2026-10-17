"""Verify the frozen source profile and its imported proof probes."""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
allowed = {"propext", "Classical.choice", "Quot.sound"}
source = root / "lean/MicroCFTA/SourceRecursiveIntersectionSourceProfile.lean"
expected = "8222f95c88388aae6cc47957f8f482f8da6fd17db224d8f5a76bb47876af0943"
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
assert digest(source) == expected
assert (evidence / "source-profile-direct-6.log").read_bytes() == b""
for label, count in [("public", 32), ("kernels", 2)]:
    text = (evidence / f"source-profile-{label}.lean").read_text()
    log = (evidence / f"source-profile-{label}-2.log").read_text()
    assert not re.search(r"error:|warning:|sorryAx|truncated|⋯|\.\.\.", log), label
    assert len(re.findall(r"^#print axioms ", text, re.M)) == count
    assert len(re.findall(r"^#check @", text, re.M)) == count
    blocks = re.findall(r"depends on axioms: \[([^\]]*)\]", log, re.S)
    empty = re.findall(r"does not depend on any axioms", log)
    assert len(blocks) + len(empty) == count
    axioms = {re.sub(r"\.\{[^}]+\}", "", name.strip()) for block in blocks for name in block.split(",") if name.strip()}
    assert axioms <= allowed, (label, axioms)
    for setting in ["linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.universes true", "pp.deepTerms true"]:
        assert "set_option " + setting in text, (label, setting)
    limit = re.search(r"set_option pp.maxSteps (\d+)", text)
    assert limit and int(limit.group(1)) >= 1000000
    print(label, count, "pairs clean; axioms", sorted(axioms))
log = (evidence / "source-profile-canonical-final.log").read_text()
assert "Build completed successfully (1174 jobs)." in log
assert not re.search(r"error:|sorryAx", log)
manifest = evidence / "source-profile-manifest.json"
if manifest.exists():
    for item in json.loads(manifest.read_text())["files"]:
        path = root / item["path"]
        assert digest(path) == item["sha256"], item["path"]
        assert path.stat().st_size == item["bytes"], item["path"]
    print("frozen manifest entries match")
print("PASS: final source profile, strict source, canonical target, public and integration probes")
