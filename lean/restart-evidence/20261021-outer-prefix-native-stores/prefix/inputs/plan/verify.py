#!/usr/bin/env python3
"""Verify the source-only unfinished-prefix store plan."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def relative(value: str) -> Path:
    result = Path(value)
    assert not result.is_absolute() and ".." not in result.parts, value
    return result


def check(path: Path, pin: dict) -> None:
    data = path.read_bytes()
    assert len(data) == pin["bytes"] and sha(data) == pin["sha256"], str(path)


def normalized(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text())
    assert manifest["finalized"] and manifest["source_only"]
    assert manifest["owned_lean_lake_commands"] == manifest["owned_public_pairs"] == 0
    assert manifest["implementation_authorized_by_this_package"] is False
    for pin in manifest["files"]:
        check(HERE / relative(pin["path"]), pin)
    pins = json.loads((HERE / "source-pins.json").read_text())["sources"]
    assert pins == manifest["sources"]
    for pin in pins:
        snapshot = HERE / relative(pin["snapshot"])
        check(snapshot, pin)
        lines = snapshot.read_bytes().splitlines(keepends=True)
        for span in pin["reviewed_ranges"]:
            lo, hi = span["start"], span["end"]
            assert 1 <= lo <= hi <= len(lines)
            assert sha(b"".join(lines[lo-1:hi])) == span["sha256"]
        if args.live:
            check(args.root / relative(pin["path"]), pin)
    proposed = (HERE / "proposed-signature.lean.txt").read_text()
    assert re.findall(r"^theorem (\w+)", proposed, re.M) == ["reached"]
    assert "namespace MicroCFTA.SourceCurrentOuterPrefixNativeStores" in proposed
    assert "open SourceCurrentOuterExecutionAncestry (Reached)" in proposed
    assert "open SourceCurrentOuterActiveAncestry" not in proposed
    assert "SourceCurrentOuterActiveAncestry.Reached" not in proposed
    assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b| := by", proposed)
    old = (HERE / "inputs/root/lean/MicroCFTA/SourceCurrentOuterInitialPrefix.lean").read_text()
    old_type = old.split("theorem reached ", 1)[1].split(" := by", 1)[0]
    old_output = old_type.split("    ∃ next final current,", 1)[1]
    new_output = proposed.split("    ∃ next final current,", 1)[1]
    old_retained = new_output.split("      NativeSupport (caller last)", 1)[0].rstrip()
    assert old_retained.endswith("∧")
    old_retained = old_retained[:-1]
    assert normalized(old_output) == normalized(old_retained)
    for law in ("NativeSupport (caller first)", "History empty (caller first)",
                "MergeStored (caller first).merge", "MergeSupport (caller first).merge",
                "UnionNormal (caller first)", "NativeSupport (caller last)",
                "Nonempty (History empty (caller last)", "MergeStored (caller last).merge",
                "MergeSupport (caller last).merge", "UnionNormal (caller last)"):
        assert law in proposed, law
    outer = HERE / "inputs/root/lean/MicroCFTA/SourceCurrentOuterNativeStores.lean"
    assert sha(outer.read_bytes()) == "b9f7f87df92990b460708bd71fb5f56085bc3b28b97c0a0d96ae1e12f6156f46"
    execution = (HERE / "inputs/root/lean/MicroCFTA/SourceCurrentOuterExecutionAncestry.lean").read_text()
    literal = execution.split("inductive Step ", 1)[1].split("inductive Reached ", 1)[0]
    assert "childrenGraph" not in literal and "edgeGraph" not in literal
    for case in ("node_evaluate", "body_rows", "rows_edge", "rows_tail", "descendants_children",
                 "children_walk", "walk_head", "walk_tail"):
        assert "| " + case in literal
    print(json.dumps({"status": "PASS", "live": args.live, "source_only": True,
                      "proposed_public_heads": ["MicroCFTA.SourceCurrentOuterPrefixNativeStores.reached"],
                      "new_public_pairs": 0, "owned_lean_lake_commands": 0,
                      "local_pins": len(manifest["files"]), "root_pins": len(pins),
                      "old_resource_output_retained": True, "implementation_proved": False,
                      "manifest_sha256": sha((HERE / "manifest.json").read_bytes())}, indent=2))


if __name__ == "__main__":
    main()
