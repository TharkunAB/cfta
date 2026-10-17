"""Verify the frozen callback erasure source and selected imported checks."""
from pathlib import Path
import hashlib
import json
import re

here = Path(__file__).resolve().parent
root = here.parents[2]
manifest = json.loads((here / "callback-erasure-manifest.json").read_text())
assert len(manifest["entries"]) == manifest["entry_count"]
for entry in manifest["entries"]:
    raw = (root / entry["path"]).read_bytes()
    assert len(raw) == entry["bytes"], entry["path"]
    assert hashlib.sha256(raw).hexdigest() == entry["sha256"], entry["path"]

source = root / "lean/MicroCFTA/SourceCurrentNativeCallbackErasure.lean"
assert source.read_bytes() == (here / "callback-erasure-direct-2.source.lean").read_bytes()
assert hashlib.sha256(source.read_bytes()).hexdigest() == "33a654079ed23f616c2935b5942d9f789d1b31f2bfaeaecc7ee78a9cdd6c8b60"
assert (here / "callback-erasure-direct-2.log").stat().st_size == 0
assert not re.search(r"\b(sorry|axiom)\b", source.read_text())
assert "Build completed successfully (533 jobs)." in (here / "callback-erasure-canonical-1.log").read_text()

selected = ["callback-erasure-direct-2", "callback-erasure-canonical-1", "callback-erasure-public-full2", "callback-erasure-kernels-4"]
peaks = (here / "callback-erasure-peaks.txt").read_text().splitlines()
for stem in selected:
    meta = json.loads((here / f"{stem}.json").read_text())
    assert meta["exit_code"] == 0
    assert meta["caps"] == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
    assert any(f"{stem}.sh " in line and line.endswith(" 0") for line in peaks), stem

options = ["linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.universes true", "pp.deepTerms true", "pp.proofs.threshold 254", "pp.maxSteps 10000000"]
for stem, count, prints in [("callback-erasure-public-full2", 7, 7), ("callback-erasure-kernels-4", 2, 0)]:
    probe = (here / f"{stem}.source.lean").read_text()
    log = (here / f"{stem}.log").read_text()
    assert all(f"set_option {option}" in probe for option in options)
    assert len(re.findall(r"^#check @", probe, re.M)) == count
    assert len(re.findall(r"^#print axioms ", probe, re.M)) == count
    assert len(re.findall(r"^#print (?!axioms )", probe, re.M)) == prints
    assert not re.search(r"error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|\.\.\.", log)
    blocks = re.findall(r"depends on axioms: \[([^\]]*)\]", log, re.S)
    assert len(blocks) + log.count("does not depend on any axioms") == count
    for block in blocks:
        axioms = {re.sub(r"\.\{[^}]+\}", "", name.strip()) for name in block.split(",") if name.strip()}
        assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, axioms

for stem in ["callback-erasure-direct-1", "callback-erasure-kernels-1", "callback-erasure-kernels-2", "binder-origins-search-1"]:
    assert "error" in (here / f"{stem}.log").read_text()
    assert json.loads((here / f"{stem}.json").read_text())["exit_code"] == 1
assert "(648, 1961, 794, [])" in (here / "binder-origins-search-2.log").read_text()
assert manifest["public_pairs"] == 7 and manifest["integration_pairs"] == 2
assert manifest["search_is_general_proof"] is False
print(f"PASS: {manifest['entry_count']} hashes; strict2 empty; canonical533; full public7; constructed nested/warm2; explicit8options; standard axioms; finite search kept separate")
