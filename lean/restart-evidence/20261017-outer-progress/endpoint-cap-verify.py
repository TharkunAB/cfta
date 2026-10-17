"""Verify the frozen primary endpoint cap component."""
from pathlib import Path
import hashlib
import json
import re

directory = Path(__file__).resolve().parent
root = directory.parents[2]
manifest = json.loads((directory / "endpoint-cap-manifest.json").read_text())
assert len(manifest["entries"]) == manifest["entry_count"]
for entry in manifest["entries"]:
    raw = (root / entry["path"]).read_bytes()
    assert len(raw) == entry["bytes"], entry["path"]
    assert hashlib.sha256(raw).hexdigest() == entry["sha256"], entry["path"]
source = (root / "lean/MicroCFTA/SourceCurrentPrimaryEndpointCap.lean").read_bytes()
assert source == (directory / "endpoint-cap-direct-3.source.lean").read_bytes()
assert hashlib.sha256(source).hexdigest() == "e18c58d403a5ef1c2b6abc93b4647562ac2436667c73ef1e1ffec51f65c69f17"
assert (directory / "endpoint-cap-direct-3.log").stat().st_size == 0
assert (directory / "endpoint-cap-kernel-strict-1.log").stat().st_size == 0
for number in [1, 2]:
    assert "error:" in (directory / f"endpoint-cap-direct-{number}.log").read_text()
    assert "Failed to connect to bus:" in (directory / f"endpoint-cap-canonical-{number}.log").read_text()
canonical = (directory / "endpoint-cap-canonical-3.log").read_text()
for expected in ["memory.max=4294967296", "memory.high=4294967296", "memory.swap.max=0", "Build completed successfully (1087 jobs)."]:
    assert expected in canonical
for stem, pairs, proofs in [("endpoint-cap-public-1", 4, True), ("endpoint-cap-kernels-5", 1, False)]:
    probe = (directory / f"{stem}.source.lean").read_text()
    log = (directory / f"{stem}.log").read_text()
    assert not re.search(r"error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|\.\.\.", log)
    assert len(re.findall(r"^#check @", probe, re.M)) == pairs
    assert len(re.findall(r"^#print axioms ", probe, re.M)) == pairs
    assert len(re.findall(r"^#print (?!axioms )", probe, re.M)) == (pairs if proofs else 0)
    for option in ["pp.explicit", "pp.fullNames", "pp.proofs", "pp.universes", "pp.deepTerms"]:
        assert f"set_option {option} true" in probe
    assert "set_option pp.proofs.threshold 254" in probe
    assert "set_option pp.maxSteps 10000000" in probe
    blocks = re.findall(r"depends on axioms: \[([^\]]*)\]", log, re.S)
    assert len(blocks) + log.count("does not depend on any axioms") == pairs
    for block in blocks:
        axioms = {re.sub(r"\.\{[^}]+\}", "", name.strip()) for name in block.split(",") if name.strip()}
        assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, axioms
for number in [1, 2, 3]:
    assert "error:" in (directory / f"endpoint-cap-kernels-{number}.log").read_text()
assert not re.search(r"\b(sorry|axiom)\b", source.decode())
kernel = (directory / "endpoint-cap-kernels-5.source.lean").read_text()
for term in ["constructed_positive_endpoint", "[value, value, .reference .depth] [[0], [1]]", "endpoint_cap heap", "not_cap_zero", "closed_verified expression", "built_done"]:
    assert term in kernel
assert kernel.split("set_option pp.explicit true")[0] == (directory / "endpoint-cap-kernel-strict-1.source.lean").read_text()
print(f"PASS: {manifest['entry_count']} hashes; strict3 empty; capped canonical1087; public4 full signatures/proofs; own source-built integration1; standard axioms")
