#!/usr/bin/env python3
"""Verify the source-only owner prefix decomposition plan."""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def relative(value: str) -> Path:
    path = Path(value)
    assert not path.is_absolute() and ".." not in path.parts, value
    return path

def check(path: Path, pin: dict) -> None:
    assert path.is_file() and path.stat().st_size == pin["bytes"] and sha(path) == pin["sha256"], str(path)

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text())
    assert manifest["finalized"] and manifest["source_only"]
    assert manifest["lean_jobs"] == manifest["canonical_jobs"] == manifest["runtime_jobs"] == manifest["public_pairs"] == 0
    assert manifest["official_edits"] is False
    for pin in manifest["files"]:
        check(HERE / relative(pin["path"]), pin)
    sources = json.loads((HERE / "source-pins.json").read_text())["sources"]
    assert sources == manifest["sources"] and len(sources) == 6
    for pin in sources:
        snapshot = HERE / relative(pin["snapshot"])
        check(snapshot, pin)
        lines = snapshot.read_bytes().splitlines(keepends=True)
        assert len(lines) == pin["lines"]
        for span in pin["reviewed_ranges"]:
            lo, hi = span["start"], span["end"]
            assert 1 <= lo <= hi <= len(lines)
            assert hashlib.sha256(b"".join(lines[lo-1:hi])).hexdigest() == span["sha256"]
        if args.live:
            check(args.root / relative(pin["path"]), pin)
    proposal = (HERE / "proposed-signature.lean.txt").read_text()
    assert len(proposal.splitlines()) == 46
    assert sha(HERE / "proposed-signature.lean.txt") == "04c66ebb2e2285c5ab0459e058a47346d7145fead1dcaf2d015be70537fdcd96"
    assert re.findall(r"^theorem (\w+)", proposal, re.M) == ["first_child"]
    assert "namespace MicroCFTA.SourceCurrentOuterOwnerPrefix" in proposal
    assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|trustCompiler|Context|Good|Frame|Room)\b|:= by|_private", proposal)
    assert "ownerRows = skippedRows ++ original :: rest" in proposal
    assert "parented.children.take slot" in proposal and "parented.children[slot]? = some child" in proposal
    assert "(handle,.evaluate captured,running)" in proposal
    assert "(.body childFuel captured running)" in proposal
    original = (HERE / "reviewed-plan-original.md").read_text()
    expected = original.replace("OuterPositionalDispatch.walk_indexed` (32–88)", "OuterPositionalDispatch.walk_indexed` (40–92)").replace("about10 lines", "about 10 lines").replace("implementation:200–300", "implementation: 200–300")
    assert (HERE / "plan.md").read_text() == expected
    assert not list(HERE.glob("*.lean")) and not list(HERE.glob("*.olean")) and not list(HERE.glob("*.log"))
    print(json.dumps({"status": "PASS", "live": args.live, "local_pins": len(manifest["files"]), "root_pins": len(sources), "source_ranges": sum(len(p["reviewed_ranges"]) for p in sources), "lean_jobs": 0, "canonical_jobs": 0, "runtime_jobs": 0, "public_pairs": 0, "proposed_public_head": "MicroCFTA.SourceCurrentOuterOwnerPrefix.first_child", "manifest_sha256": sha(HERE / "manifest.json")}, indent=2))

if __name__ == "__main__":
    main()
