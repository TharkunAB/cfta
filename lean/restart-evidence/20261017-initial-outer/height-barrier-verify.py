"""Verify the frozen source-accepted Required height witness."""
from pathlib import Path
import hashlib
import json
import re

directory = Path(__file__).resolve().parent
root = directory.parents[2]
manifest = json.loads((directory / "height-barrier-manifest.json").read_text())
assert manifest["entry_count"] == len(manifest["entries"])
for entry in manifest["entries"]:
    raw = (root / entry["path"]).read_bytes()
    assert len(raw) == entry["bytes"], entry["path"]
    assert hashlib.sha256(raw).hexdigest() == entry["sha256"], entry["path"]

source = (root / "lean/MicroCFTA/SourceCurrentOuterHeightBarrier.lean").read_bytes()
assert source == (directory / "height-barrier-direct-2.source.lean").read_bytes()
assert hashlib.sha256(source).hexdigest() == "a11836c07873cebefb685cbd54461d879ba09961b31b64d39390aaa5ec9f817a"
assert (directory / "height-barrier-direct-2.log").stat().st_size == 0
assert "error:" in (directory / "height-barrier-direct-1.log").read_text()
assert "Build completed successfully (1193 jobs)." in (directory / "height-barrier-canonical-1.log").read_text()

probe = (directory / "height-barrier-public-1.source.lean").read_text()
log = (directory / "height-barrier-public-1.log").read_text()
assert not re.search(r"error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|\.\.\.", log)
for option in ["pp.explicit", "pp.fullNames", "pp.proofs", "pp.universes", "pp.deepTerms"]:
    assert f"set_option {option} true" in probe
assert "set_option pp.proofs.threshold 254" in probe
assert "set_option pp.maxSteps 10000000" in probe
assert len(re.findall(r"^#check @", probe, re.M)) == 2
assert len(re.findall(r"^#print (?!axioms )", probe, re.M)) == 2
assert len(re.findall(r"^#print axioms ", probe, re.M)) == 2
blocks = re.findall(r"depends on axioms: \[([^\]]*)\]", log, re.S)
assert len(blocks) == 2
for block in blocks:
    axioms = {re.sub(r"\.\{[^}]+\}", "", name.strip()) for name in block.split(",") if name.strip()}
    assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, axioms
for name in ["supported_required_growth", "not_required_height_nonincreasing"]:
    assert f"theorem MicroCFTA.SourceCurrentOuterHeightBarrier.{name}" in log
assert "SourceCurrentMuEndpoint.classMeets true source reaches 1" in source.decode()
assert "SourceEqualityRequiredWorkerSound.require_graph 3 0" in source.decode()
assert "height input = 0 ∧ height output = 1" in source.decode()
assert not re.search(r"\b(sorry|axiom)\b", source.decode())
print(f"PASS: {manifest['entry_count']} hashes; strict2 empty; canonical1193; public2 full signatures/proofs/standard axioms; own source-built witness")
