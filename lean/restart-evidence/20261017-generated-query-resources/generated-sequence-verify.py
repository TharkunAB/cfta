#!/usr/bin/env python3
"""Verify the frozen generated-result sequence evidence without a build."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
manifest = json.loads((HERE / "generated-sequence-manifest.json").read_text())
assert len(manifest["entries"]) == manifest["entry_count"]
seen = set()
for entry in manifest["entries"]:
    relative = entry["path"]
    assert relative not in seen, relative
    seen.add(relative)
    path = ROOT / relative
    data = path.read_bytes()
    assert len(data) == entry["bytes"], relative
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], relative
metadata = json.loads((HERE / "generated-sequence-validation.json").read_text())
source = ROOT / metadata["final_source"]
log = (ROOT / metadata["final_log"]).read_text()
assert metadata["final_exit_code"] == 0
assert source.read_bytes() == (HERE / "generated-sequence-kernels-8.source.lean").read_bytes()
assert not re.search(r"error(?:\(|:)|warning:|sorryAx", log)
assert source.read_bytes().endswith(b"\n") and not source.read_bytes().endswith(b"\n\n")
assert "set_option pp.proofs true" in source.read_text()
assert "set_option pp.explicit true" in source.read_text()
assert "set_option pp.fullNames true" in source.read_text()
assert "set_option pp.universes true" in source.read_text()
assert "set_option pp.deepTerms true" in source.read_text()
assert "set_option linter.all true" in source.read_text()
assert "set_option pp.maxSteps 10000000" in source.read_text()
pairs = re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.M | re.S)
assert len(pairs) == 2, len(pairs)
for name, axioms in pairs:
    assert f"#print axioms {name}" in source.read_text()
    assert f"#check @{name}" in source.read_text()
    actual = [re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in axioms.split(",")]
    assert set(actual) <= {"propext", "Classical.choice", "Quot.sound"}, (name, actual)
    assert re.search(r"^" + re.escape(name) + r"\s*:", log, re.M), name
print(f"PASS: {manifest['entry_count']} hashes; 2 complete signature/axiom pairs; final diagnostics 0")
