import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = "SourceCurrentCappedHeadPositivePosition.lean"
HEAD = "MicroCFTA.SourceCurrentCappedHeadPositivePosition.head"


def check(base, entry):
    data = (base / entry["path"]).read_bytes()
    assert len(data) == entry["bytes"] and hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]


parser = argparse.ArgumentParser()
parser.add_argument("--root", type=Path, default=Path("/home/tritlo/Code/mcfta"))
parser.add_argument("--live", action="store_true")
args = parser.parse_args()
manifest = json.loads((HERE / "head-manifest.json").read_text())
for item in manifest["files"]:
    check(HERE, item)
for item in manifest["sources"]:
    check(HERE / "inputs/root", item)
    if args.live:
        check(args.root, item)
assert json.loads((HERE / "head-source-pins.json").read_text())["files"] == manifest["sources"]
selection = json.loads((HERE / "head-selection.json").read_text())
assert selection["finalized"] and selection["public_heads"] == [HEAD]
assert selection["lean_jobs"] == len(selection["attempts"]) == 2
assert selection["strict_jobs"] == selection["public_jobs"] == selection["new_public_pairs"] == 1
assert selection["canonical_jobs"] == selection["failed_checks"] == selection["warning_checks"] == selection["constructed_pairs"] == 0
assert not selection["unselected_successes"]
source = (HERE / SOURCE).read_text()
assert hashlib.sha256(source.encode()).hexdigest() == selection["source_sha256"]
assert source == (HERE / (selection["selected_strict"] + ".source.lean")).read_text()
assert len(source.splitlines()) == 60
assert re.findall(r"^theorem (\w+)", source, re.M) == ["head"]
assert not re.search(r"^(?:def|inductive|structure|axiom) |\bsorry\b|\badmit\b|native_decide|trustCompiler", source, re.M)
for producer in ["SourceEqualityProjectionCosts.read_effects", "EqualityLeafProjectionPhysical.makeNode_edges",
                 "SourceEqualityRequiredCache.node_ordinary", "SourceCurrentCappedProjectionPositivePosition.root",
                 "SourceCurrentCappedProjectionPositivePosition.child"]:
    assert source.count(producer) == 1, producer
assert source.count("Project.root") == 2
assert source.count("List.mem_iff_getElem?.mp") == 2
assert "Read value before rows middle := .done fuel exposed" in source
assert "(pure_keeps before semantic.ready) guards depth bounded" in source
for stem, exit_code in selection["attempts"].items():
    meta = json.loads((HERE / (stem + ".json")).read_text())
    assert meta["exit_code"] == exit_code == 0
    assert meta["wrapper"][meta["wrapper"].index("--mem") + 1] == "4G"
    assert meta["wrapper"][meta["wrapper"].index("--time") + 1] == "5m"
    assert json.loads((HERE / meta["limits"]).read_text()) == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
    usage = json.loads((HERE / (stem + ".usage.json")).read_text())
    assert usage["age_seconds"] < 120 and usage["remaining_percent"] > 1
    assert hashlib.sha256((HERE / meta["source"]).read_bytes()).hexdigest() == meta["sha256"]
    assert "-Dlinter.all=true" in meta["command"]
    assert meta["command"][0].endswith("leanprover--lean4---v4.34.1/bin/lean")
assert not (HERE / (selection["selected_strict"] + ".log")).read_bytes()
printer = (HERE / (selection["selected_public"] + ".source.lean")).read_text()
assert printer.startswith(source)
for option in ["linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]:
    assert "set_option " + option in printer
for directive in ["#check @", "#print ", "#print axioms "]:
    assert printer.count(directive + HEAD + "\n") == 1
log = (HERE / (selection["selected_public"] + ".log")).read_text()
assert len(log.encode()) == selection["public_log_bytes"] == 100046
assert not re.search(r"sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.", log)
axioms = re.search(r"'" + re.escape(HEAD) + r"' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log)
assert axioms
names = set() if axioms.group(1) is None else set(re.split(r",\s*", re.sub(r"\.\{[^}]*\}", "", axioms.group(1)).strip()))
assert names <= {"propext", "Classical.choice", "Quot.sound"}, names
printed = log.split("theorem " + HEAD, 1)[1].split("'" + HEAD + "'", 1)[0]
typ, body = printed.split(":=", 1)
assert typ.strip() and body.strip() and "_private" not in typ
print(json.dumps({"status": "PASS", "pins": len(manifest["files"]) + len(manifest["sources"]),
                  "lean_jobs": 2, "new_public_pairs": 1, "constructed_pairs": 0,
                  "failed_checks": 0, "warning_checks": 0, "canonical_jobs": 0, "live": args.live}))
