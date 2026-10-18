import hashlib
import importlib.util
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

manifest_path = HERE / "structural-kernels-manifest.json"
manifest = json.loads(manifest_path.read_text())
for item in manifest["files"]:
    path = ROOT / item["path"]
    assert path.is_file(), item["path"]
    assert path.stat().st_size == item["bytes"], item["path"]
    assert sha(path) == item["sha256"], item["path"]
selection = json.loads((HERE / "structural-kernels-selection.json").read_text())
assert selection["status"] == "final"
source = HERE / selection["source"]
assert sha(source) == selection["source_sha256"]
strict = json.loads((HERE / (selection["strict"] + ".json")).read_text())
assert strict["exit_code"] == 0
assert (HERE / strict["log"]).read_bytes() == b""
assert (HERE / strict["source"]).read_bytes() == source.read_bytes()
spec = importlib.util.spec_from_file_location("owned_probe_tools", HERE / "structural-kernels-probe-tools.py")
tools = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tools)
tools.check_limits(selection["strict"])
for group in selection["selected_groups"]:
    tools.check_group(group)
    meta = json.loads((HERE / (group["name"] + ".json")).read_text())
    assert (HERE / meta["source"]).read_bytes().startswith(source.read_bytes())
for i in range(2, 10):
    tools.check_limits("structural-kernels-direct-" + str(i))
text = source.read_text()
private = re.search(r"private theorem checked_witness(.*?) := by", text, re.S).group(1)
public = re.search(r"theorem descendant_events(.*?) := checked_witness formulas solver", text, re.S).group(1)
assert private == public, "Private and public statements differ"
assert selection["counts"]["constructed"] == 1
assert selection["counts"]["owned_production_public"] == selection["counts"]["auxiliary"] == 0
report = {"status":"PASS", "pins":len(manifest["files"]), "manifest_sha256":sha(manifest_path),
    "constructed_pairs":1, "owned_production_public_pairs":0, "auxiliary_pairs":0,
    "selected_full_groups":1, "selected_strict_logs":1, "strict_literal_zero":True,
    "private_public_statements_identical":True}
print(json.dumps(report, sort_keys=True))
