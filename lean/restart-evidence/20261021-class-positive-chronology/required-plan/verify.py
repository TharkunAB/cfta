#!/usr/bin/env python3
"""Check this source-only Required-entry plan and its exact source ranges."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / "manifest.json").read_text())
    for entry in manifest["files"]:
        path = Path(entry["path"])
        assert not path.is_absolute() and ".." not in path.parts
        data = (here / path).read_bytes()
        assert len(data) == entry["bytes"] and sha(data) == entry["sha256"], str(path)
    pins = json.loads((here / "source-pins.json").read_text())
    assert pins["sources"] == manifest["sources"]
    ranges = []
    for source in pins["sources"]:
        path, snapshot = Path(source["path"]), Path(source["snapshot"])
        assert not path.is_absolute() and ".." not in path.parts
        assert not snapshot.is_absolute() and ".." not in snapshot.parts
        data = (here / snapshot).read_bytes()
        assert len(data) == source["bytes"] and sha(data) == source["sha256"], str(path)
        lines = data.splitlines(keepends=True)
        for span in source["reviewed_ranges"]:
            start, end = span["start"], span["end"]
            assert 1 <= start <= end <= len(lines)
            assert sha(b"".join(lines[start - 1:end])) == span["sha256"]
            ranges.append({"path": source["path"], **span})
        if args.live:
            assert sha((args.root / path).read_bytes()) == source["sha256"], str(path)
    assert ranges == json.loads((here / "ranges.json").read_text())["ranges"]
    selection = json.loads((here / "selection.json").read_text())
    assert selection["finalized"] and not selection["proposed_result_proved"]
    assert not selection["official_edits"] and not selection["implementation_authorized_in_this_task"]
    assert selection["proposed_public_heads"] == ["pass"]
    for law in ("current", "native_support", "causal_history"):
        assert selection[f"scan_{law}_supplied"]
        assert not selection[f"prepared_{law}_supplied"]
    for field in ("new_lean_commands", "new_canonical_commands", "new_public_pairs", "new_constructed_pairs"):
        assert pins[field] == selection[field] == 0
    dependency = next(item for item in pins["sources"] if item["path"].endswith("/SourceCurrentClassPositiveChronology.lean"))
    assert dependency["sha256"] == selection["dependency_sha256"]
    plan = (here / "plan.md").read_text()
    for clause in (
        "SOURCE-ONLY PLAN", "The proposed adapter is unproved.",
        "RequiredGuard.children", "CurrentNative.advance", "NativePositiveSupportAdvance.advance",
        "RequiredPublicationHistory.children", "RequiredForestPositive.requireAll",
        "No false trace is required on prepared", "Rel selected",
        "These predicates are different.", "Two positive outputs can retain different ORIGINAL witnesses",
    ):
        assert clause in plan, clause
    signature = (here / "proposed-signature.lean.txt").read_text()
    assert signature.count("theorem pass") == 1
    assert "(current : Current scan)" in signature
    assert "(supported : NativeSupport scan.native.machine.heap scan.native)" in signature
    assert "(causal : History empty scan.native.machine.heap)" in signature
    assert "(guards :" not in signature and "(preparedCurrent :" not in signature
    print(json.dumps({
        "status": "PASS", "live": args.live,
        "root_sources": len(pins["sources"]), "reviewed_ranges": len(ranges),
        "pins": len(manifest["files"]) + len(manifest["sources"]),
        "new_lean_commands": 0, "new_canonical_commands": 0,
        "new_public_pairs": 0, "new_constructed_pairs": 0,
        "proposal_proved": False, "prepared_laws_derived_in_proposal": True,
        "manifest_sha256": sha((here / "manifest.json").read_bytes()),
    }, indent=2))


if __name__ == "__main__":
    main()
