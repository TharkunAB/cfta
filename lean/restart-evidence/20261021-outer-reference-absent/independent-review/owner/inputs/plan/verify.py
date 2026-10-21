#!/usr/bin/env python3
"""Verify the source-only reference and absent-node consumer plan."""
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
    assert manifest["finalized"] and manifest["source_only"]
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
    for key in ("compiler_jobs", "lake_jobs", "canonical_jobs", "runtime_jobs", "new_theorems"):
        assert status[key] == 0
    assert status["source_only"] and not status["implementation_included"]
    assert status["public_consumer_unproved"] and status["private_cuts_unproved"]
    assert not status["closure_dependency_claimed_checked"] and not status["adequacy_or_completion_claimed"]
    selected = json.loads((HERE / "selection.json").read_text())
    assert selected["finalized"] and selected["source_reviewed"] and not selected["elaborated"]
    assert not selected["implementation_authorized_by_this_package"]
    for path, key in (("plan.md", "plan_sha256"), ("proposed-signature.lean.txt", "signature_sha256"),
                      ("proposed-private-cuts.lean.txt", "private_cuts_sha256"),
                      ("proposed-context.lean.txt", "context_sha256")):
        assert digest((HERE / path).read_bytes()) == selected[key]
    plan = (HERE / "plan.md").read_bytes()
    signature = (HERE / "proposed-signature.lean.txt").read_bytes()
    cuts = (HERE / "proposed-private-cuts.lean.txt").read_bytes()
    assert len(plan.splitlines()) == 29 and len(signature.splitlines()) == 27
    assert signature.count(b"theorem no_reference_or_node_absent\n") == 1
    assert b"SourceCurrentOuterClosedInputs.NodeStored" in signature
    assert b"SourceCurrentOuterClosedInputs.InputsClosed first" in signature
    assert b".failed (.unexpectedReference name) after" in signature
    assert b".failed (.nodeMemo handle .absent) after" in signature
    assert b"private theorem reference_cut\n" in cuts and b"private theorem absent_cut\n" in cuts
    dependency = json.loads((HERE / "dependency-status.json").read_text())
    assert not dependency["checked"] and not dependency["official_artifact_claimed"]
    assert not dependency["copied_full_package"]
    assert digest((HERE / "inputs/closure-plan/manifest.json").read_bytes()) == dependency["copied_plan_manifest_sha256"]
    assert digest((HERE / "inputs/closure-plan/proposed-signatures.lean.txt").read_bytes()) == dependency["copied_public_proposal_sha256"]
    review = json.loads((HERE / "review-clearance.json").read_text())
    assert review["implementation_hard_stop"] == 250
    assert review["original_plan_and_proposal_unchanged"]
    scope = json.loads((HERE / "scope-addendum.json").read_text())
    assert scope["total_source_hard_stop"] == 250 and scope["public_heads"] == 1
    assert scope["one_local_joint_inverse"] and not scope["implementation_authorized"]
    assert scope["official_compiled_closure_required"]
    assert scope["root_and_guard_complete_final_source_review_required_before_compiler"]
    assert scope["stop_before_any_compiler_or_further_implementation"]
    assert scope["closure_dependency_and_all_proposals_unproved"]
    print(json.dumps({
        "status": "PASS", "live": args.live, "source_only": True,
        "local_pins": len(manifest["files"]), "root_pins": len(pins),
        "reviewed_ranges": intervals, "compiler_jobs": 0, "runtime_jobs": 0,
        "new_theorems": 0, "consumer_and_private_cuts_unproved": True,
        "closure_dependency_claimed_checked": False,
        "absence_arm_protocol_only": True, "adequacy_or_completion_claimed": False,
        "authored_foundations_disclosed": True,
        "manifest_sha256": digest((HERE / "plan-manifest.json").read_bytes()),
    }, indent=2))


if __name__ == "__main__":
    main()
