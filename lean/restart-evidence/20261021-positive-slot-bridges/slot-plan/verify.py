import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def check(base, entry):
    data = (base / entry["path"]).read_bytes()
    assert len(data) == entry["bytes"] and hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]


parser = argparse.ArgumentParser()
parser.add_argument("--root", type=Path, default=Path("/home/tritlo/Code/mcfta"))
parser.add_argument("--live", action="store_true")
args = parser.parse_args()
manifest = json.loads((HERE / "manifest.json").read_text())
for item in manifest["files"]:
    check(HERE, item)
for item in manifest["sources"]:
    check(HERE / "inputs/root", item)
    if args.live:
        check(args.root, item)
assert json.loads((HERE / "source-pins.json").read_text())["files"] == manifest["sources"]
selection = json.loads((HERE / "selection.json").read_text())
assert selection["finalized"]
assert selection["lean_jobs"] == selection["new_public_pairs"] == selection["constructed_pairs"] == 0
assert selection["target_public_heads"] == ["MicroCFTA.SourceCurrentRawCorridorSharedTargetPositivePositions.force_receipt"]
for item in selection["proposed_dependency_sources"]:
    check(HERE, item)
signature = (HERE / "proposed-contract.lean.txt").read_text()
for required in ["(receipt : SourceCurrentAllocatedSharedTargetForce.Receipt", "(stored : CapStored before)",
                 "(supported : NativeSupport before.checked.native.machine.heap before.checked.native)",
                 "(causal : History empty before.checked.native.machine.heap)",
                 "(mergePositive : MergeSupport before.memo)", "(slots : ∀ a t, before.targets a = some t"]:
    assert required in signature, required
assert signature.count("values[index]? = some original ∧ PositiveAt original (path ++ q)") == 2
print(json.dumps({"status": "PASS", "pins": len(manifest["files"]) + len(manifest["sources"]),
                  "lean_jobs": 0, "new_public_pairs": 0, "live": args.live}))
