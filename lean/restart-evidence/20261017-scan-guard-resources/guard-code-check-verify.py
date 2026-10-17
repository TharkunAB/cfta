"""Verify the independent local native guard code review."""
import hashlib
import json
from pathlib import Path
import re

p = Path(__file__).resolve().parent
root = p.parents[2]
m = json.loads((p / "guard-code-check-manifest.json").read_text())
assert len(m["entries"]) == m["entry_count"]
for item in m["entries"]:
    assert hashlib.sha256((root / item["path"]).read_bytes()).hexdigest() == item["sha256"], item
assert (root / "lean/MicroCFTA/SourceCurrentNativeGuardCode.lean").read_bytes() == (p / "native-guard-code-direct-2.source.lean").read_bytes()
assert (p / "native-guard-code-direct-2.log").stat().st_size == 0
assert "Build completed successfully (1067 jobs)" in (p / "native-guard-code-canonical-1.log").read_text()
for name, pairs in [("guard-code-check-public-1", 9), ("guard-code-check-kernels-2", 2)]:
    source = (p / (name + ".source.lean")).read_text()
    log = (p / (name + ".log")).read_text()
    assert not re.search(r"error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|\.\.\.", log)
    assert len(re.findall(r"^#check @", source, re.M)) == pairs
    assert len(re.findall(r"^#print axioms ", source, re.M)) == pairs
    for option in ["pp.explicit", "pp.fullNames", "pp.proofs", "pp.universes", "pp.deepTerms"]:
        assert "set_option " + option + " true" in source
    assert "set_option pp.maxSteps 10000000" in source
    blocks = re.findall(r"depends on axioms: \[([^\]]*)\]", log, re.S)
    assert len(blocks) + log.count("does not depend on any axioms") == pairs
    for block in blocks:
        axioms = {re.sub(r"\.\{[^}]+\}", "", n.strip()) for n in block.split(",") if n.strip()}
        assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, axioms
assert "error:" in (p / "guard-code-check-kernels-1.log").read_text()
kernel = (p / "guard-code-check-kernels-2.source.lean").read_text()
for fragment in ["FieldAvailable.receipts fields initial_ready.valid", "SourceEqualityNativeDemand.body_complete", "SourceCurrentNativeGuardCode.body_fields", "SourceCurrentNativeGuardCode.compileNode_fields (fun _ => False)", "SourceEqualityConstraintAllocation.Ready", "SourceEqualityConjoinAllocation.readback first = request.left.entry.key.constraint"]:
    assert fragment in kernel, fragment
print(f"PASS: {m['entry_count']} hashes; public9 + own source-body/node kernels2; root strict empty; canonical1067")
