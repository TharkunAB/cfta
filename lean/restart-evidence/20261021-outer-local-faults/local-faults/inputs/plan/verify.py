#!/usr/bin/env python3
"""Check the source-only fault plan without running a proof command."""
from __future__ import annotations
import argparse
import hashlib
import json
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
    sources = json.loads((HERE / "source-pins.json").read_text())["sources"]
    index = json.loads((HERE / "source-index.json").read_text())
    assert sources == manifest["sources"] and len(sources) == len(index) == 11
    assert sum(len(source["reviewed_ranges"]) for source in sources) == 17
    for source, cited in zip(sources, index, strict=True):
        assert source["id"] == cited["id"] and source["path"] == cited["path"]
        snapshot = HERE / relative(source["snapshot"])
        check(snapshot, source)
        lines = snapshot.read_bytes().splitlines(keepends=True)
        assert len(lines) == source["lines"]
        assert len(source["reviewed_ranges"]) == len(cited["ranges"])
        for span, pair in zip(source["reviewed_ranges"], cited["ranges"], strict=True):
            first, last = pair
            assert (first, last) == (span["start"], span["end"])
            assert 1 <= first <= last <= len(lines)
            block = b"".join(lines[first - 1:last])
            assert hashlib.sha256(block).hexdigest() == span["sha256"]
            expected = "".join(f"{n:5d} {line.decode()}" for n, line in enumerate(lines[first - 1:last], first))
            assert (HERE / relative(span["excerpt"])).read_text() == expected
        if args.live:
            check(args.root / relative(source["path"]), source)
    scope = json.loads((HERE / "scope.json").read_text())
    selection = json.loads((HERE / "selection.json").read_text())
    assert selection == manifest["selection"] and scope == manifest["scope"]
    assert selection["source_only"] and selection["status"] == "unimplemented_unelaborated_proposal"
    for name in ["lean_jobs", "lake_jobs", "canonical_jobs", "runtime_jobs", "public_pairs", "constructed_pairs", "official_edits"]:
        assert selection[name] == 0
    assert scope["new_lean_jobs"] == scope["canonical_jobs"] == scope["runtime_jobs"] == scope["official_edits"] == 0
    assert selection["selected_lean_attempts"] == selection["selected_public_attempts"] == []
    assert scope["pending_dependency"]["status"] == "source_only_unproved_at_cue"
    assert len((HERE / "plan.md").read_text().splitlines()) == 37
    assert len((HERE / "proposed-signature.lean.txt").read_text().splitlines()) == 21
    assert sha(HERE / "plan.md") == selection["plan_sha256"] == "4d20f61bb6ee5dea0a3f5f20c884cbe004d73263962ab67b39c7610e631dbbf8"
    assert sha(HERE / "proposed-signature.lean.txt") == selection["proposed_signature_sha256"] == "47107835ae80dc64559e2785085117826e517f1d01355b5c6803ff9d9fe55695"
    stop = json.loads((HERE / "scope-stop-erratum.json").read_text())
    assert stop["total_source_hard_stop"] == selection["total_source_hard_stop"] == 250
    assert stop["stop_before"] == ["compiler", "further_implementation"]
    assert stop["explicit_scope_review_required"] and not stop["implementation_authorized"] and not stop["compiler_authorized"]
    assert stop["original_plan_sha256"] == selection["plan_sha256"]
    assert stop["original_signature_sha256"] == selection["proposed_signature_sha256"]
    assert not list(HERE.glob("*.lean")) and not list(HERE.glob("*.olean")) and not list(HERE.glob("*.log"))
    print(json.dumps(dict(status="PASS", live=args.live, source_only=True, local_pins=len(manifest["files"]), root_pins=11, source_ranges=17, lean_jobs=0, canonical_jobs=0, runtime_jobs=0, proposed_public_heads=["failed_cases"], completion_proved=False, manifest_sha256=sha(HERE / "manifest.json")), indent=2))

if __name__ == "__main__":
    main()
