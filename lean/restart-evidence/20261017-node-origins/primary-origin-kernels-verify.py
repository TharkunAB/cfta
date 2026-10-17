#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json
import re

here = Path(__file__).resolve().parent
root = here.parents[2]
manifest = json.loads(here.joinpath("primary-origin-kernels-manifest.json").read_text())
for entry in manifest["entries"]:
    path = root / entry["path"]
    assert hashlib.sha256(path.read_bytes()).hexdigest() == entry["sha256"], entry["path"]
strict = "primary-origin-kernel-strict-1"
assert here.joinpath(strict + ".log").stat().st_size == 0
assert json.loads(here.joinpath(strict + ".json").read_text())["exit_code"] == 0
stem = "primary-origin-kernels-5"
assert json.loads(here.joinpath(stem + ".json").read_text())["exit_code"] == 0
source = here.joinpath(stem + ".source.lean").read_text()
assert source == here.joinpath("primary-origin-kernels.lean").read_text()
assert source.split("\n#check",1)[0] == here.joinpath(strict + ".source.lean").read_text()
assert "set_option pp.proofs.threshold 254" in source
assert source.count("\n#check @") == 2
assert source.count("\n#print axioms ") == 2
log = here.joinpath(stem + ".log").read_text()
assert not re.search(r"warning:|error:|sorryAx|⋯|…|\.\.\.|truncat", log)
blocks = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log)
assert len(blocks) == 2
expected = {"MicroCFTA.RequiredPrimaryOriginKernels.selected_finite_and_recursive",
            "MicroCFTA.RequiredPrimaryOriginKernels.constructed_empty_open"}
assert {name for name, _ in blocks} == expected
allowed = {"propext", "Classical.choice", "Quot.sound"}
for _, block in blocks:
    names = {re.sub(r"\.\{[^}]*\}","",name.strip()) for name in block.split(",")}
    assert names <= allowed, names
for attempt in range(1,5):
    name = f"primary-origin-kernels-{attempt}"
    metadata = json.loads(here.joinpath(name + ".json").read_text())
    assert metadata["exit_code"] != 0
    assert here.joinpath(name + ".source.lean").is_file()
    assert here.joinpath(name + ".log").is_file()
print(f"PASS {len(manifest['entries'])} entries; kernels2; strict log empty; four failed attempts preserved")
