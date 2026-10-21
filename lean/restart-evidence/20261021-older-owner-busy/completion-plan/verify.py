#!/usr/bin/env python3
"""Check this source-only completion audit without running Lean."""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def relative(name: str) -> Path:
    path = Path(name)
    assert not path.is_absolute() and ".." not in path.parts, name
    return path

def check(path: Path, pin: dict) -> None:
    assert path.is_file(), str(path)
    assert path.stat().st_size == pin["bytes"], str(path)
    assert sha(path) == pin["sha256"], str(path)

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text())
    assert manifest["finalized"] and manifest["source_only"]
    for pin in manifest["files"]:
        check(HERE / relative(pin["path"]), pin)
    pins = json.loads((HERE / "source-pins.json").read_text())["sources"]
    index = json.loads((HERE / "source-index.json").read_text())["sources"]
    assert pins == manifest["sources"] and len(pins) == len(index) == 21
    for source, cited in zip(pins, index, strict=True):
        assert source["id"] == cited["id"] and source["path"] == cited["path"]
        snapshot = HERE / relative(source["snapshot"])
        check(snapshot, source)
        lines = snapshot.read_bytes().splitlines(keepends=True)
        assert len(lines) == source["lines"]
        assert len(source["reviewed_ranges"]) == len(cited["ranges"])
        for span, original in zip(source["reviewed_ranges"], cited["ranges"], strict=True):
            first, last = span["start"], span["end"]
            assert first == original["start"] and last == original["end"]
            assert 1 <= first <= last <= len(lines)
            assert hashlib.sha256(b"".join(lines[first - 1:last])).hexdigest() == span["sha256"]
        if args.live:
            check(args.root / relative(source["path"]), source)
    scope = json.loads((HERE / "scope.json").read_text())
    assert scope == manifest["scope"]
    for name in ["lean_jobs", "lake_jobs", "canonical_jobs", "runtime_jobs", "public_pairs", "constructed_pairs", "new_proof_declarations"]:
        assert scope[name] == 0
    for name in ["official_edits", "completion_proved", "rank_implies_adequate_fuel_claimed", "closure_counterexample_constructed", "closed_request_transport_proved", "capacity_contract_resolved"]:
        assert scope[name] is False
    assert scope["source_only"] and scope["proposed_public_head"] is None
    plan = (HERE / "plan.md").read_text()
    assert len(plan.splitlines()) == scope["plan_lines"] == 37 <= 45
    assert sha(HERE / "plan.md") == scope["plan_sha256"] == "9dcedb9dcc520b660e104eea34e5f5f36f4ae07be651c57a13cd4161ff6a3810"
    ids = {source["id"] for source in pins}
    assert set(re.findall(r"\[(S[0-9]+)(?::|\])", plan)) <= ids
    assert "value.free=[]" in plan and "Bound references inside an opaque Mu are permitted" in plan
    assert "not a constructed counterexample" in plan and "No defensible sole public completion header" in plan
    assert not list(HERE.glob("*.lean")) and not list(HERE.glob("*.olean")) and not list(HERE.glob("*.log"))
    assert not list(HERE.glob("proposed-signature*"))
    print(json.dumps(dict(status="PASS", live=args.live, local_pins=len(manifest["files"]), root_pins=len(pins), source_ranges=sum(len(x["reviewed_ranges"]) for x in pins), lean_jobs=0, lake_jobs=0, canonical_jobs=0, runtime_jobs=0, public_pairs=0, completion_proved=False, proposed_public_head=None, manifest_sha256=sha(HERE / "manifest.json")), indent=2))

if __name__ == "__main__":
    main()
