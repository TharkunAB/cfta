#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json
import re

here = Path(__file__).resolve().parent
root = here.parents[2]
manifest = json.loads(here.joinpath("finite-exposure-manifest.json").read_text())
for entry in manifest["entries"]:
    assert hashlib.sha256(root.joinpath(entry["path"]).read_bytes()).hexdigest() == entry["sha256"], entry["path"]
for stem in ["union-normal-direct-3", "finite-exposure-direct-2", "finite-exposure-kernel-strict-1"]:
    assert here.joinpath(stem + ".log").stat().st_size == 0, stem
    assert json.loads(here.joinpath(stem + ".json").read_text())["exit_code"] == 0
allowed = {"propext", "Classical.choice", "Quot.sound"}
for stem, count in [("finite-exposure-public-1",18), ("finite-exposure-kernels-3",3)]:
    text = here.joinpath(stem + ".log").read_text()
    assert not re.search(r"warning:|error:|sorryAx|⋯|…|\.\.\.|truncat", text)
    blocks = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text)
    independent = re.findall(r"'([^']+)' does not depend on any axioms", text)
    assert len(blocks) + len(independent) == count, (stem,len(blocks),len(independent))
    for _, block in blocks:
        names = {re.sub(r"\.\{[^}]*\}","",name.strip()) for name in block.split(",")}
        assert names <= allowed, names
    assert json.loads(here.joinpath(stem + ".json").read_text())["exit_code"] == 0
assert json.loads(here.joinpath("finite-exposure-canonical-1.json").read_text())["exit"] == 0
assert "Build completed successfully (1082 jobs)." in here.joinpath("finite-exposure-canonical-1.log").read_text()
print(f"PASS {len(manifest['entries'])} entries; public18 + kernels3; final strict logs empty")
