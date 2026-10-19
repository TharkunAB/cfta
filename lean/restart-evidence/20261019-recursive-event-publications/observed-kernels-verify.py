import hashlib
import importlib.util
import json
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PREFIX = "observed-kernels"


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
assert selection["status"] == "final"
source = HERE / selection["source"]
assert sha(source) == selection["source_sha256"]
spec = importlib.util.spec_from_file_location("owned_observed_kernel_probe", HERE / (PREFIX + "-probe-tools.py"))
probe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe)
for attempt in selection["attempts"]:
    stem = attempt["name"]
    meta = json.loads((HERE / (stem + ".json")).read_text())
    assert meta["exit_code"] == attempt["exit_code"], stem
    assert sha(HERE / meta["source"]) == meta["sha256"], stem
    assert meta["command"][0].endswith("leanprover--lean4---v4.34.1/bin/lean"), stem
    assert meta["command"][1] == "-Dlinter.all=true", stem
    assert meta["wrapper"][:5] == [
        "/home/tritlo/Code/heavy-management/bin/capped", "--mem", "4G", "--time", "5m"
    ], stem
    probe.check_limits(stem)
strict = json.loads((HERE / (selection["strict"] + ".json")).read_text())
assert strict["exit_code"] == 0
assert (HERE / strict["log"]).read_bytes() == b""
assert (HERE / strict["source"]).read_bytes() == source.read_bytes()
for group in selection["selected_groups"]:
    probe.check_group(group)
    meta = json.loads((HERE / (group["name"] + ".json")).read_text())
    assert (HERE / meta["source"]).read_bytes().startswith(source.read_bytes())
for path, expected in selection["dependency_sources"].items():
    assert sha(ROOT / path) == expected, path
for path, stem in selection["reused_stricts"].items():
    meta = json.loads((HERE / (stem + ".json")).read_text())
    assert meta["exit_code"] == 0
    assert (HERE / meta["log"]).read_bytes() == b""
    assert (HERE / meta["source"]).read_bytes() == (ROOT / path).read_bytes()
    assert sha(HERE / meta["source"]) == meta["sha256"]
    probe.check_limits(stem)
for group in selection["reused_groups"]:
    probe.check_group(group)
    meta = json.loads((HERE / (group["name"] + ".json")).read_text())
    assert sha(HERE / meta["source"]) == meta["sha256"]
for stem in selection["reused_canonical"]:
    meta = json.loads((HERE / (stem + ".json")).read_text())
    assert meta["exit_code"] == 0
    assert meta["command"][0].endswith("leanprover--lean4---v4.34.1/bin/lake")
    assert meta["wrapper"][:5] == [
        "/home/tritlo/Code/heavy-management/bin/capped", "--mem", "4G", "--time", "5m"
    ]
    log = (HERE / meta["log"]).read_text()
    assert "Build completed successfully" in log
    assert re.findall(r"^warning: (.*)$", log, re.M) == [
        "MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean:24:5: Variable name `inputs` is not explicitly referenced."
    ]
    assert not re.search(r"^error:", log, re.M)
    probe.check_limits(stem)
text = source.read_text()
private = re.search(r"private theorem checked_witness(.*?) := by", text, re.S).group(1)
public = re.search(r"theorem nonroot_publication(.*?) := checked_witness", text, re.S).group(1)
assert private == public
comparison = json.loads((HERE / (PREFIX + "-statement-comparison.json")).read_text())
assert comparison["status"] == "identical"
assert comparison["final_sha256"] == sha(source)
old_source = HERE / comparison["old_source"]
assert sha(old_source) == comparison["old_sha256"]
old_text = old_source.read_text()
old_public = re.search(r"theorem nonroot_publication(.*?) := checked_witness", old_text, re.S).group(1)
assert old_public == public
assert hashlib.sha256(public.encode()).hexdigest() == comparison["public_statement_sha256"]
start, stop = "private def plain", "private theorem built_done"
assert text.split(start, 1)[1].split(stop, 1)[0] == old_text.split(start, 1)[1].split(stop, 1)[0]
assert "run_cmd" not in text and "stderrAsMessages" not in text
peaks = (HERE / selection["immutable_peaks"]).read_text().splitlines()
assert len(peaks) == len(selection["attempts"])
assert all(line.split()[2] == "4G" for line in peaks)
assert [int(line.split()[-1]) for line in peaks] == [attempt["exit_code"] for attempt in selection["attempts"]]
assert selection["counts"] == {
    "owned_production_public": 0, "constructed": 1, "auxiliary": 0,
    "selected_full_groups": 1, "selected_strict_logs": 1,
    "owned_jobs": len(selection["attempts"]), "owned_lean_jobs": len(selection["attempts"]),
    "wrapper_blocked_jobs": 0,
}
print(json.dumps({
    "status": "PASS", "pins": len(manifest["files"]),
    "manifest_sha256": sha(manifest_path), "constructed_pairs": 1,
    "owned_production_public_pairs": 0, "owned_jobs": len(selection["attempts"]),
    "owned_lean_jobs": len(selection["attempts"]), "wrapper_blocked_jobs": 0,
    "strict_literal_zero": True, "private_public_statements_identical": True,
}, sort_keys=True))
