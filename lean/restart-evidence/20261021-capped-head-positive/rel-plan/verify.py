#!/usr/bin/env python3
"""Check the source snapshots and source-only scope of this plan."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    root = args.root.resolve()
    manifest = json.loads((here / "manifest.json").read_text())
    for entry in manifest["files"]:
        relative = Path(entry["path"])
        assert not relative.is_absolute() and ".." not in relative.parts
        data = (here / relative).read_bytes()
        assert len(data) == entry["bytes"], str(relative)
        assert digest(data) == entry["sha256"], str(relative)
    pins = json.loads((here / "source-pins.json").read_text())
    count = 0
    for entry in pins["sources"]:
        relative = Path(entry["path"])
        assert not relative.is_absolute() and ".." not in relative.parts
        data = (here / entry["snapshot"]).read_bytes()
        assert len(data) == entry["bytes"] and digest(data) == entry["sha256"], entry["path"]
        lines = data.splitlines(keepends=True)
        for selected in entry["reviewed_ranges"]:
            start, end = selected["start"], selected["end"]
            assert 1 <= start <= end <= len(lines)
            assert digest(b"".join(lines[start - 1:end])) == selected["sha256"]
            count += 1
        if args.live:
            assert digest((root / relative).read_bytes()) == entry["sha256"], entry["path"]
    for entry in pins["candidates"]:
        data = (here / entry["snapshot"]).read_bytes()
        assert len(data) == entry["bytes"] and digest(data) == entry["sha256"], entry["role"]
    selection = json.loads((here / "selection.json").read_text())
    assert selection["finalized"] and not selection["proposed_class_result_proved"]
    assert not selection["official_edits"]
    for key in ("new_lean_commands", "new_public_pairs", "new_constructed_pairs"):
        assert selection[key] == pins[key] == 0
    plan = (here / "plan.md").read_text()
    for required in (
        "SOURCE-ONLY PLAN", "completed `ClassReads`", "Rel [record.paths]",
        "common suffix", "History.retain", "NoNewMu",
        "The proposed class theorem and its private induction remain unproved.",
        "not backwards positive ancestry certificates", "The returned existential witnesses can differ.",
    ):
        assert required in plan, required
    print(json.dumps({
        "status": "PASS", "live": args.live, "root_sources": len(pins["sources"]),
        "candidate_snapshots": len(pins["candidates"]), "reviewed_ranges": count,
        "new_lean_commands": 0, "new_public_pairs": 0, "new_constructed_pairs": 0,
        "class_theorem_status": "unproved plan", "manifest_sha256": digest((here / "manifest.json").read_bytes()),
    }, indent=2))


if __name__ == "__main__":
    main()
