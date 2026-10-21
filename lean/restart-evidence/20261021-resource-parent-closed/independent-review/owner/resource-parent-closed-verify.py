#!/usr/bin/env python3
"""Verify the Parent child closure proof and its portable evidence."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PREFIX = "resource-parent-closed"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((HERE / (PREFIX + "-manifest.json")).read_text())
    assert manifest["finalized"]
    for pin in manifest["files"]:
        data = (HERE / pin["path"]).read_bytes()
        assert len(data) == pin["bytes"] and digest(data) == pin["sha256"], pin["path"]
    selected = json.loads((HERE / (PREFIX + "-selection.json")).read_text())
    assert selected["finalized"]
    source = (HERE / selected["source"]).read_bytes()
    assert digest(source) == selected["source_sha256"] and len(source.splitlines()) == 101
    if args.live:
        assert digest((args.root / selected["official_path"]).read_bytes()) == digest(source)
    result = json.loads(subprocess.check_output([sys.executable, str(HERE / "check-full-public.py")], cwd="/"))
    assert result == json.loads((HERE / "full-public-readback.json").read_text())
    assert result["source_sha256"] == digest(source) and len(result["heads"]) == 1
    assert result["all_eight_printer_settings"] and result["no_omissions"]
    head = result["heads"][0]
    assert head["check_print_type_identity"] and head["unique_actual_lambda_body_delimiter"]
    assert not head["private_public_type_names"]
    assert set(head["actual_axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
    assert head["actual_axioms"] == selected["actual_axioms_by_head"][head["head"]]
    ledger = json.loads((HERE / "attempt-ledger.json").read_text())
    assert len(ledger["attempts"]) == ledger["actual_lean_jobs"] == 2
    assert ledger["failed_jobs"] == ledger["warning_jobs"] == ledger["canonical_jobs"] == ledger["runtime_jobs"] == 0
    for attempt in ledger["attempts"]:
        receipt = json.loads((HERE / attempt["receipt"]).read_text())
        usage = json.loads((HERE / attempt["usage"]).read_text())
        limits = json.loads((HERE / attempt["limits"]).read_text())
        assert receipt["exit_code"] == attempt["exit_code"] == 0
        assert digest((HERE / receipt["source"]).read_bytes()) == receipt["sha256"]
        assert limits == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
        assert usage["age_seconds"] <= 600 and usage["remaining_percent"] > 1
        assert receipt["wrapper"][:5] == ["/home/tritlo/Code/heavy-management/bin/capped", "--mem", "4G", "--time", "5m"]
        assert "-Dlinter.all=true" in receipt["command"]
        assert not re.search(r"\bwarning(?:\([^)]*\))?:", (HERE / attempt["raw_log"]).read_text())
    strict = json.loads((HERE / (selected["selected_strict"] + ".json")).read_text())
    assert strict["sha256"] == digest(source)
    assert (HERE / (selected["selected_strict"] + ".log")).stat().st_size == 0
    expected = (HERE / "inputs/plan/proposed-signature.lean.txt").read_bytes()
    start = source.index(b"theorem children\n")
    end = source.index(b" := by\n", start)
    assert source[start:end] == expected
    text = source.decode()
    for call in ("SourceCurrentActualParentBranchCases.edge_cases", "SourceCurrentActualParentSelectedCertificates.selected_certificates",
                 "SourceEqualityRequiredExecution.requireAll_complete", "SourceCurrentConjunctionRequiredActual.required_unique",
                 "SourceCurrentAllocatedClassPass.Pass.verified", "receipt.domains [] preparedClosed"):
        assert text.count(call) == 1, call
    assert source == (HERE / "parent-closed-source-only.lean.txt").read_bytes()
    command = [sys.executable, str(HERE / "inputs/plan/verify.py"), "--root", str(args.root)]
    if args.live:
        command.append("--live")
    plan = json.loads(subprocess.check_output(command, cwd="/"))
    assert plan["status"] == "PASS"
    print(json.dumps({
        "status": "PASS", "live": args.live, "local_pins": len(manifest["files"]),
        "root_pins": plan["root_pins"] + 1, "actual_lean_jobs": 2, "failed_jobs": 0,
        "warning_jobs": 0, "canonical_jobs": 0, "runtime_jobs": 0, "constructed_pairs": 0,
        "full_public_heads": 1, "actual_axioms_by_head": selected["actual_axioms_by_head"],
        "all_eight_settings": True, "exact_public_type_identity": True,
        "same_historical_parent_and_children": True, "no_new_edge_ledger_or_current_cut": True,
        "all_prefix_and_node_memo_closure_unproved": True,
        "fuel_adequacy_and_completion_unproved": True, "authored_foundations_disclosed": True,
        "manifest_sha256": digest((HERE / (PREFIX + "-manifest.json")).read_bytes()),
    }, indent=2))


if __name__ == "__main__":
    main()
