#!/usr/bin/env python3
"""Verify the complete Local public printer evidence without writes."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / "local-printer-final-manifest.json").read_text())
for entry in manifest["entries"]:
    data = (ROOT / entry["path"]).read_bytes()
    assert len(data) == entry["bytes"], entry["path"]
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]
old_path = HERE / "local-check-manifest.json"
assert hashlib.sha256(old_path.read_bytes()).hexdigest() == "d253cf53e2c45565bdc1bb7ea2a6cce55af9de71839b6d57ce05cca0dc5997db"
old = json.loads(old_path.read_text())
assert len(old["entries"]) == 55
for entry in old["entries"]:
    data = (ROOT / entry["path"]).read_bytes()
    assert len(data) == entry["bytes"], entry["path"]
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]

stem = "local-check-public-2"
source = (HERE / (stem + ".source.lean")).read_text()
assert source == (HERE / "local-check-public-1.source.lean").read_text().replace(
    "set_option pp.proofs true", "set_option pp.proofs true\nset_option pp.proofs.threshold 254"
)
metadata = json.loads((HERE / (stem + ".json")).read_text())
assert metadata["exit"] == 0
assert metadata["command"][-1] == str(HERE / (stem + ".source.lean"))
assert metadata["command"][1] == "-Dlinter.all=true"
log = (HERE / (stem + ".log")).read_text()
assert not re.search(r"⋯|…|\.{3}|truncat", log, re.I)
assert not re.search(r"\bsorryAx\b|: (?:error|warning)(?:\(|:)", log)
declarations = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log, re.S)
declarations += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", log)]
assert len(declarations) == 12
assert len({name for name, _ in declarations}) == 12
for name, axioms in declarations:
    axes = re.sub(r"\.\{[^}]*\}", "", axioms)
    assert {x.strip() for x in axes.split(",") if x.strip()} <= {
        "propext", "Classical.choice", "Quot.sound"
    }, (name, axioms)
    assert f"#print axioms {name}" in source
    assert f"#check @{name}" in source
    assert f"#print {name}" in source
    assert re.search(re.escape(name) + r"(?:\.\{[^}]*\})?\s*:", log)
assert "saved ⋯ memos final" in (HERE / "local-check-public-1.log").read_text()
assert not re.search(r"⋯|…|\.{3}|truncat", (HERE / "local-check-kernels-6.log").read_text(), re.I)
print(f"PASS: {len(manifest['entries'])} printer entries; 12 complete public pairs; old 55-entry manifest unchanged")
