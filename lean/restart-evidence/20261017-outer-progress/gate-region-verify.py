"""Verify the actual-gate hereditary-region component."""

import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


manifest = json.loads((HERE / "gate-region-manifest.json").read_text())
for entry in manifest["entries"]:
    path = ROOT / entry["path"]
    assert path.stat().st_size == entry["bytes"], path
    assert digest(path) == entry["sha256"], path
module = ROOT / "lean/MicroCFTA/SourceCurrentGatePlainRegion.lean"
assert digest(module) == "aa76a1b61f6b5b9e9a3f6c5c84b627ea7602b37e3e6257ce9b0a5d7f3cd664c0"
assert module.read_bytes() == (HERE / "gate-region-direct-2.source.lean").read_bytes()
assert (HERE / "gate-region-direct-2.log").read_bytes() == b""
assert "Build completed successfully (1079 jobs)." in (HERE / "gate-region-canonical-1.log").read_text()
assert "error" in (HERE / "gate-region-direct-1.log").read_text()
assert "error" in (HERE / "gate-region-kernels-1.log").read_text()

allowed = {"propext", "Classical.choice", "Quot.sound"}
for stem, count, public in [("gate-region-public-1", 4, True), ("gate-region-kernels-2", 1, False)]:
    source = (HERE / f"{stem}.source.lean").read_text()
    log = (HERE / f"{stem}.log").read_text()
    assert not re.search(r"error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|…|\.\.\.", log), stem
    checks = re.findall(r"^#check @(\S+)", source, re.M)
    assert len(checks) == count
    assert re.findall(r"^#print axioms (\S+)", source, re.M) == checks
    assert re.findall(r"^#print (?!axioms )(\S+)", source, re.M) == (checks if public else [])
    for option in ["linter.all", "pp.explicit", "pp.fullNames", "pp.proofs", "pp.universes", "pp.deepTerms"]:
        assert f"set_option {option} true" in source, (stem, option)
    assert "set_option pp.proofs.threshold 254" in source
    assert "set_option pp.maxSteps 10000000" in source
    blocks = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", log, re.S)
    assert len(blocks) + log.count("does not depend on any axioms") == count
    for block in blocks:
        observed = {re.sub(r"\.\{[^}]+\}", "", name.strip()) for name in block.split(",") if name.strip()}
        assert observed <= allowed, observed
print(f"PASS: {len(manifest['entries'])} hashes; strict2 empty; canonical1079; public4; constructed1; standard axioms")
