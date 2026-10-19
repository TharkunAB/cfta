import hashlib
import importlib.util
import json
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

manifest_path = HERE / "event-kernels-manifest.json"
manifest = json.loads(manifest_path.read_text())
assert manifest["status"] == "final"
assert len({item["path"] for item in manifest["files"]}) == len(manifest["files"])
for item in manifest["files"]:
    path = ROOT / item["path"]
    assert path.is_file(), item["path"]
    assert path.stat().st_size == item["bytes"], item["path"]
    assert sha(path) == item["sha256"], item["path"]
assert not any(item["path"].endswith("/event-kernels-peaks.txt") for item in manifest["files"])
selection = json.loads((HERE / "event-kernels-selection.json").read_text())
assert selection["status"] == "final"
source = HERE / selection["source"]
assert sha(source) == selection["source_sha256"]
strict = json.loads((HERE / (selection["strict"] + ".json")).read_text())
assert strict["exit_code"] == 0
assert (HERE / strict["log"]).read_bytes() == b""
assert (HERE / strict["source"]).read_bytes() == source.read_bytes()
spec = importlib.util.spec_from_file_location("owned_event_probe_tools", HERE / "event-kernels-probe-tools.py")
probe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe)
for index in range(1, 2):
    stem = "event-kernels-direct-" + str(index)
    meta = json.loads((HERE / (stem + ".json")).read_text())
    assert meta["exit_code"] == 0, stem
    assert sha(HERE / meta["source"]) == meta["sha256"], stem
    assert meta["command"][0].endswith("leanprover--lean4---v4.34.1/bin/lean"), stem
    assert meta["command"][1] == "-Dlinter.all=true", stem
    assert meta["wrapper"][0:5] == ["/home/tritlo/Code/heavy-management/bin/capped", "--mem", "4G", "--time", "5m"], stem
    probe.check_limits(stem)
for group in selection["selected_groups"]:
    probe.check_group(group)
    meta = json.loads((HERE / (group["name"] + ".json")).read_text())
    assert (HERE / meta["source"]).read_bytes().startswith(source.read_bytes())
    assert sha(HERE / meta["source"]) == meta["sha256"]
for stem in selection["reused_canonical"]:
    meta = json.loads((HERE / (stem + ".json")).read_text())
    assert meta["exit_code"] == 0
    log = (HERE / meta["log"]).read_text()
    assert re.findall(r"^warning: (.*)$", log, re.M) == ["MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced."]
    assert "Build completed successfully" in log
    probe.check_limits(stem)
text = source.read_text()
private = re.search(r"private theorem checked_witness(.*?) := by", text, re.S).group(1)
public = re.search(r"theorem native_event_sources(.*?) := checked_witness formulas solver", text, re.S).group(1)
assert private == public, "Private and public statements differ"
peaks = (HERE / selection["immutable_peaks"]).read_text().splitlines()
assert len(peaks) == 2
assert [line.split()[-1] for line in peaks] == ["0", "0"]
assert all(line.split()[2] == "4G" for line in peaks)
assert selection["counts"] == {"owned_production_public": 0, "constructed": 1, "auxiliary": 0, "selected_full_groups": 1, "selected_strict_logs": 1, "owned_lean_jobs": 2}
assert len(selection["selected_groups"]) == 1
assert selection["selected_groups"][0]["pairs"] == 1
print(json.dumps({"status": "PASS", "pins": len(manifest["files"]), "manifest_sha256": sha(manifest_path), "constructed_pairs": 1, "owned_production_public_pairs": 0, "auxiliary_pairs": 0, "selected_full_groups": 1, "selected_strict_logs": 1, "owned_lean_jobs": 2, "strict_literal_zero": True, "private_public_statements_identical": True, "immutable_peaks_rows": 2}, sort_keys=True))
