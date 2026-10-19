import hashlib
import importlib.util
import json
import re
import sys
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PREFIX = "publication-kernels"
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
manifest_path = HERE / (PREFIX + "-manifest.json")
manifest = json.loads(manifest_path.read_text())
assert manifest["status"] == "final"
assert len({item["path"] for item in manifest["files"]}) == len(manifest["files"])
for item in manifest["files"]:
    path = ROOT / item["path"]
    assert path.is_file(), item["path"]
    assert path.stat().st_size == item["bytes"], item["path"]
    assert sha(path) == item["sha256"], item["path"]
assert not any(item["path"].endswith("/" + PREFIX + "-peaks.txt") for item in manifest["files"])
selection = json.loads((HERE / (PREFIX + "-selection.json")).read_text())
source = HERE / selection["source"]
assert selection["status"] == "final"
assert sha(source) == selection["source_sha256"]
spec = importlib.util.spec_from_file_location("owned_publication_kernel_probe", HERE / (PREFIX + "-probe-tools.py"))
probe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe)
for attempt in selection["attempts"]:
    stem = attempt["name"]
    meta = json.loads((HERE / (stem + ".json")).read_text())
    assert meta["exit_code"] == attempt["exit_code"], stem
    assert sha(HERE / meta["source"]) == meta["sha256"], stem
    assert meta["command"][0].endswith("leanprover--lean4---v4.34.1/bin/lean"), stem
    assert meta["command"][1] == "-Dlinter.all=true", stem
    assert meta["wrapper"][:5] == ["/home/tritlo/Code/heavy-management/bin/capped", "--mem", "4G", "--time", "5m"], stem
    if attempt["kind"] == "wrapper-blocked":
        assert "Failed to connect to bus: Operation not permitted" in (HERE / meta["log"]).read_text()
        assert not (HERE / meta["limits"]).exists()
    else:
        probe.check_limits(stem)
strict = json.loads((HERE / (selection["strict"] + ".json")).read_text())
assert strict["exit_code"] == 0
assert (HERE / strict["log"]).read_bytes() == b""
assert (HERE / strict["source"]).read_bytes() == source.read_bytes()
for group in selection["selected_groups"]:
    probe.check_group(group)
    meta = json.loads((HERE / (group["name"] + ".json")).read_text())
    assert (HERE / meta["source"]).read_bytes().startswith(source.read_bytes())
for stem in selection["reused_canonical"]:
    meta = json.loads((HERE / (stem + ".json")).read_text())
    assert meta["exit_code"] == 0
    log = (HERE / meta["log"]).read_text()
    assert "Build completed successfully" in log
    assert re.findall(r"^warning: (.*)$", log, re.M) == ["MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced."]
    assert not re.search(r"^error:", log, re.M)
    probe.check_limits(stem)
text = source.read_text()
private = re.search(r"private theorem checked_witness(.*?) := by", text, re.S).group(1)
public = re.search(r"theorem nested_publication(.*?) := checked_witness", text, re.S).group(1)
assert private == public
peaks = (HERE / selection["immutable_peaks"]).read_text().splitlines()
assert len(peaks) == 2
assert [line.split()[-1] for line in peaks] == ["0", "0"]
assert all(line.split()[2] == "4G" for line in peaks)
assert selection["counts"] == {"owned_production_public": 0, "constructed": 1, "auxiliary": 0, "selected_full_groups": 1, "selected_strict_logs": 1, "owned_jobs": 2, "owned_lean_jobs": 2, "wrapper_blocked_jobs": 0}
print(json.dumps({"status": "PASS", "pins": len(manifest["files"]), "manifest_sha256": sha(manifest_path), "constructed_pairs": 1, "owned_production_public_pairs": 0, "owned_jobs": 2, "owned_lean_jobs": 2, "wrapper_blocked_jobs": 0, "strict_literal_zero": True, "private_public_statements_identical": True}, sort_keys=True))
