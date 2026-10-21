#!/usr/bin/env python3
"""Verify this source-only conditional outer-closure plan without Lean."""
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
    assert path.is_file() and path.stat().st_size == pin["bytes"], str(path)
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
    assert pins == manifest["sources"] and len(pins) == len(index) == 20
    for source, cited in zip(pins, index, strict=True):
        assert source["id"] == cited["id"] and source["path"] == cited["path"]
        assert not source["path"].endswith("SourceCurrentResourceParentClosed.lean")
        snapshot = HERE / relative(source["snapshot"])
        check(snapshot, source)
        lines = snapshot.read_bytes().splitlines(keepends=True)
        assert len(lines) == source["lines"]
        for span, original in zip(source["reviewed_ranges"], cited["ranges"], strict=True):
            first, last = span["start"], span["end"]
            assert first == original["start"] and last == original["end"]
            assert 1 <= first <= last <= len(lines)
            assert hashlib.sha256(b"".join(lines[first-1:last])).hexdigest() == span["sha256"]
        if args.live:
            check(args.root / relative(source["path"]), source)
    scope = json.loads((HERE / "scope.json").read_text())
    assert scope == manifest["scope"] and scope["source_only"]
    for name in ["lean_jobs", "lake_jobs", "canonical_jobs", "runtime_jobs", "public_pairs", "constructed_pairs"]:
        assert scope[name] == 0
    for name in ["implementation_authorized", "public_type_elaborated", "official_edits", "parent_closed_claimed_checked", "parent_closed_source_pinned", "closure_preservation_claimed_proved", "completion_claimed_proved"]:
        assert scope[name] is False
    assert sha(HERE / "plan.md") == scope["plan_sha256"] == "8621a0a8330cdb74134ddd17c6f8e27e441ec6e7e94833ba67b1b798bff7625c"
    assert sha(HERE / "proposed-signatures.lean.txt") == scope["proposal_sha256"] == "40f20c3b285c132865fd4ec63a8c11429c42d9d1604301cf47dac3925b442cf5"
    assert len((HERE / "plan.md").read_text().splitlines()) == scope["plan_lines"] == 31 <= 40
    proposal = (HERE / "proposed-signatures.lean.txt").read_text()
    assert len(proposal.splitlines()) == scope["proposal_lines"] == 59
    assert re.findall(r"^def (\w+)", proposal, re.M) == scope["proposed_definitions"] == ["NodeStored", "InputsClosed"]
    assert re.findall(r"^theorem (\w+)", proposal, re.M) == scope["proposed_theorems"] == ["initial", "reached"]
    assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|:= by|_private", proposal)
    assert "request.value.free = [] → result.free = []" in proposal
    assert "NodeStored (caller last) ∧ InputsClosed last" in proposal
    status = json.loads((HERE / "dependency-status.json").read_text())
    assert status["parent_closed"]["source_pinned"] is False
    assert "UNPROVED" in status["parent_closed"]["status"]
    assert status["implementation_authorized"] is False and status["official_edits"] is False
    for name in ["lean_jobs", "lake_jobs", "canonical_jobs", "runtime_jobs"]:
        assert status[name] == 0
    stop = json.loads((HERE / "scope-stop-erratum.json").read_text())
    assert stop["plan_sha256"] == sha(HERE / "plan.md") and stop["proposal_sha256"] == sha(HERE / "proposed-signatures.lean.txt")
    assert stop["original_bytes_unchanged"] and stop["public_scope_unchanged"]
    assert stop["hard_source_stop_lines"] == 250 and stop["maximum_after_explicit_approval"] == 420
    for name in ["stop_before_compiler", "stop_before_further_implementation", "complete_partial_root_review_required", "complete_partial_independent_review_required", "explicit_remaining_scope_approval_required", "official_checked_parent_closed_required", "root_dependency_ready_cue_required"]:
        assert stop[name] is True
    for name in ["implementation_authorized", "new_public_heads_allowed", "new_framework_allowed", "dependency_status_upgraded"]:
        assert stop[name] is False
    assert sha(HERE / "scope-stop-erratum.md") == "ad610bf4e2d363a8cd46dc3425568350ccfd79a3e5291ff08886a52ffdc17707"
    assert sha(HERE / "scope-stop-erratum.json") == "83ba97560c7af07677cb1eaf43fb8879800ec7619b88ea894cafbb3cb4781922"
    assert not list(HERE.glob("*.lean")) and not list(HERE.glob("*.olean")) and not list(HERE.glob("*.log"))
    print(json.dumps(dict(status="PASS", live=args.live, local_pins=len(manifest["files"]), root_pins=len(pins), source_ranges=sum(len(x["reviewed_ranges"]) for x in pins), lean_jobs=0, lake_jobs=0, canonical_jobs=0, runtime_jobs=0, public_pairs=0, implementation_authorized=False, dependency_claimed_proved=False, hard_source_stop_lines=250, manifest_sha256=sha(HERE / "manifest.json")), indent=2))

if __name__ == "__main__":
    main()
