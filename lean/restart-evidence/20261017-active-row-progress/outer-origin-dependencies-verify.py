#!/usr/bin/env python3
"""Verify the frozen origin-dependency component without running Lean."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
manifest = json.loads((HERE / "outer-origin-dependencies-manifest.json").read_text())
for entry in manifest["entries"]:
    data = (ROOT / entry["path"]).read_bytes()
    assert len(data) == entry["bytes"], entry["path"]
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]
production = ROOT / manifest["production"]
assert hashlib.sha256(production.read_bytes()).hexdigest() == manifest["source_sha256"]
assert production.read_bytes() == (HERE / "outer-origin-dependencies-direct-3.source.lean").read_bytes()
source = production.read_text()
assert len(re.findall(r"(?m)^theorem ", source)) == 4
assert not re.search(r"\b(sorry|admit|axiom)\b", source)
limits = {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
failed = set(manifest["failed_attempts"])
reports = []
for path in sorted(HERE.glob("outer-origin-dependencies-*.json")):
    report = json.loads(path.read_text())
    if "exit_code" not in report:
        continue
    stem = path.stem
    reports.append(stem)
    assert report["exit_code"] == (1 if stem in failed else 0), stem
    assert json.loads((HERE / report["limits"]).read_text()) == limits, stem
    assert report["observed_at"], stem
    assert (HERE / report["log"]).is_file(), stem
    assert report["wrapper"][0] == "/home/tritlo/Code/heavy-management/bin/capped", stem
    assert report["wrapper"][1:5] == ["--mem", "4G", "--time", "5m"], stem
    assert "/leanprover--lean4---v4.34.1/bin/" in report["command"][0], stem
    if "source" in report:
        snapshot = HERE / report["source"]
        assert hashlib.sha256(snapshot.read_bytes()).hexdigest() == report["sha256"], stem
        assert report["command"][-1] == str(snapshot), stem
        assert report["command"][1] == "-Dlinter.all=true", stem
    else:
        assert report["command"][-2:] == ["build", "MicroCFTA.SourceCurrentOuterOriginDependencies"], stem
assert failed <= set(reports)
for stem in manifest["selected_runs"]:
    assert stem in reports
    assert json.loads((HERE / (stem + ".json")).read_text())["exit_code"] == 0
for stem in ["outer-origin-dependencies-direct-3", "outer-origin-dependencies-kernels-strict-2"]:
    assert (HERE / (stem + ".log")).read_bytes() == b"", stem
canonical = (HERE / "outer-origin-dependencies-canonical-2.log").read_text()
assert "Build completed successfully (1328 jobs)." in canonical
assert len(re.findall(r"(?m)^warning:", canonical)) == 1
assert "InternedFreshOrdinaryClosedCompletion.lean:24:5" in canonical
assert not re.search(r"error:|sorryAx|failed to pretty", canonical, re.I)
options = ["linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]
for group in manifest["groups"]:
    stem = group["stem"]
    report = json.loads((HERE / (stem + ".json")).read_text())
    probe = (HERE / report["source"]).read_text()
    output = (HERE / report["log"]).read_text()
    for option in options:
        assert "set_option " + option in probe, (stem, option)
    assert not re.search(r"error:|warning:|sorryAx|failed to pretty|maximum number of steps|⋯|\.\.\.", output, re.I), stem
    for name in group["names"]:
        assert "#check @" + name in probe, (stem, name)
        assert "#print axioms " + name in probe, (stem, name)
        if group["full_proof"]:
            assert re.search(r"(?m)^#print " + re.escape(name) + r"$", probe), name
        match = re.search(r"'" + re.escape(name) + r"' depends on axioms:\s*\[(.*?)\]", output, re.S)
        assert match, (stem, name)
        axioms = {re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in match.group(1).split(",") if item.strip()}
        assert axioms <= set(manifest["allowed_axioms"]), (stem, axioms)
    assert len(group["names"]) == group["pairs"]
assert manifest["public_pairs"] == 4 and manifest["constructed_pairs"] == 2
assert manifest["probe_groups"] == len(manifest["groups"]) == 2
assert "literal_outer_prefix_and_early_stop" in (HERE / "outer-origin-dependencies-kernels-4.source.lean").read_text()
print(f"PASS: {len(manifest['entries'])} pinned entries; 4 public + 2 constructed pairs; 2 groups; all attempt receipts and effective 4 GiB limits verified.")
