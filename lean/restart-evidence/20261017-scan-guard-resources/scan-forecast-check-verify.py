"""Verify the pure Scan forecast review and typed concrete compositions."""
import hashlib
import json
from pathlib import Path
import re

p = Path(__file__).resolve().parent
root = p.parents[2]
m = json.loads((p / "scan-forecast-check-manifest.json").read_text())
assert len(m["entries"]) == m["entry_count"]
for item in m["entries"]:
    assert hashlib.sha256((root / item["path"]).read_bytes()).hexdigest() == item["sha256"], item
assert (root / "lean/MicroCFTA/SourceCurrentScanNumericForecast.lean").read_bytes() == (p / "scan-forecast-direct-4.source.lean").read_bytes()
assert (p / "scan-forecast-direct-4.log").stat().st_size == 0
assert "Build completed successfully (1562 jobs)" in (p / "scan-forecast-canonical-2.log").read_text()
for name, pairs in [("scan-forecast-check-public-1", 12), ("scan-forecast-check-kernels-8", 2)]:
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
for attempt in [3, 4, 5, 6]:
    assert re.search(r"error(?:\(|:)", (p / f"scan-forecast-check-kernels-{attempt}.log").read_text())
assert "warning:" in (p / "scan-forecast-check-kernels-7.log").read_text()
assert json.loads((p / "scan-forecast-check-kernels-3.status-correction.json").read_text())["exit_code"] == 1
for name in ["scan-forecast-check-kernels-1.status.json", "scan-forecast-check-kernels-2.status.json", "scan-forecast-check-progress-1.status.json"]:
    assert json.loads((p / name).read_text())["exit_code"] == 130
kernel = (p / "scan-forecast-check-kernels-8.source.lean").read_text()
for fragment in ["[[0, 0], [0, 1]]", "[[0], [1]]", "[.reference .depth, .empty]", "private theorem ordered_stages", "private theorem padded_stages", "theorem ordered_two_classes", "theorem padded_two_classes", "classStep_primary_ge", "classStep_secondary_ge", "schedule_alphabet_ge"]:
    assert fragment in kernel, fragment
print(f"PASS: {m['entry_count']} hashes; public12 + pure two-class compositions2; strict empty; canonical1562")
