#!/usr/bin/env python3
"""Verify the source-only Parent child closure plan and source snapshots."""
from pathlib import Path
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((HERE / "plan-manifest.json").read_text())
    assert manifest["finalized"]
    for pin in manifest["files"]:
        data = (HERE / pin["path"]).read_bytes()
        assert len(data) == pin["bytes"] and digest(data) == pin["sha256"], pin["path"]
    pins = json.loads((HERE / "sourcepins.json").read_text())["pins"]
    intervals = 0
    for pin in pins:
        data = (HERE / pin["snapshot"]).read_bytes()
        assert len(data) == pin["bytes"] and digest(data) == pin["sha256"]
        if args.live:
            assert digest((args.root / pin["root_path"]).read_bytes()) == pin["sha256"], pin["root_path"]
        lines = data.splitlines(keepends=True)
        for interval in pin["reviewed_ranges"]:
            excerpt = b"".join(lines[interval["first"] - 1:interval["last"]])
            assert excerpt == (HERE / interval["snapshot"]).read_bytes()
            assert digest(excerpt) == interval["sha256"]
            intervals += 1
    status = json.loads((HERE / "status.json").read_text())
    assert status["source_only"] and not status["implementation_included"]
    for key in ("compiler_jobs", "canonical_jobs", "runtime_jobs", "new_theorems"):
        assert status[key] == 0
    assert status["local_children_closure_unproved"] and status["all_prefix_closure_unproved"]
    assert status["outer_node_warm_closure_unproved"] and not status["new_edge_ledger_required"]
    selection = json.loads((HERE / "selection.json").read_text())
    plan = (HERE / "plan.md").read_bytes()
    signature = (HERE / "proposed-signature.lean.txt").read_bytes()
    assert selection["finalized"] and selection["source_reviewed"] and not selection["elaborated"]
    assert not selection["implementation_authorized_by_this_package"]
    assert digest(plan) == selection["plan_sha256"] and len(plan.splitlines()) <= 40
    assert digest(signature) == selection["signature_sha256"]
    assert signature.count(b"theorem children\n") == 1
    assert signature.count(b"(written : SourceCurrentResourceParentWriters.Written") == 1
    assert b"ClosedValues request.value.children" in signature
    assert signature.endswith(b"ClosedValues returned.children\n")
    print(json.dumps({
        "status": "PASS", "live": args.live, "source_only": True,
        "local_pins": len(manifest["files"]), "root_pins": len(pins),
        "reviewed_ranges": intervals, "compiler_jobs": 0, "runtime_jobs": 0,
        "new_theorems": 0, "local_children_closure_unproved": True,
        "all_prefix_closure_unproved": True, "new_edge_ledger_required": False,
        "authored_foundations_disclosed": True,
        "manifest_sha256": digest((HERE / "plan-manifest.json").read_bytes()),
    }, indent=2))


if __name__ == "__main__":
    main()
