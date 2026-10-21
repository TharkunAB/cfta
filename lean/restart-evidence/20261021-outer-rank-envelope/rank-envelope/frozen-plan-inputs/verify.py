#!/usr/bin/env python3
"""Check the source-only plan without running a proof or the proposed recurrence."""
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
    assert path.is_file() and path.stat().st_size == pin["bytes"], str(path)
    assert sha(path) == pin["sha256"], str(path)

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--live", action="store_true")
    parser.add_argument("--toolchain-source", type=Path)
    args = parser.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text())
    assert manifest["finalized"] and manifest["source_only"]
    for pin in manifest["files"]:
        check(HERE / relative(pin["path"]), pin)
    pin_data = json.loads((HERE / "source-pins.json").read_text())
    sources = pin_data["sources"]
    index = json.loads((HERE / "source-index.json").read_text())
    assert sources == manifest["sources"] and len(sources) == len(index) == 10
    assert sum(source["authority"] == "root" for source in sources) == 6
    assert sum(source["authority"] == "toolchain" for source in sources) == 4
    assert sum(len(source["reviewed_ranges"]) for source in sources) == 19
    toolchain = args.toolchain_source or Path(pin_data["toolchain_source_root"])
    for source, cited in zip(sources, index, strict=True):
        for key in ["id", "authority", "path"]:
            assert source[key] == cited[key]
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
            origin = args.root if source["authority"] == "root" else toolchain
            check(origin / relative(source["path"]), source)
    scope = json.loads((HERE / "scope.json").read_text())
    selected = json.loads((HERE / "selection.json").read_text())
    history = json.loads((HERE / "original-history.json").read_text())
    assert scope == manifest["scope"] and selected == manifest["selection"]
    assert selected["source_only"] and selected["status"] == "source_only_two_head_proposal"
    assert selected["selected_public_heads"] == ["envelope", "retains"]
    assert selected["deferred_public_heads"] == ["stage_bounds"]
    assert selected["selected_lean_attempts"] == selected["selected_public_attempts"] == []
    for key in ["lean_jobs", "lake_jobs", "canonical_jobs", "runtime_jobs", "public_pairs", "constructed_pairs", "official_edits"]:
        assert selected[key] == 0
    for key in ["envelope_defined", "retention_proved", "stage_bounds_proved", "F_constructed", "adequacy_proved", "capacity_resolved"]:
        assert selected[key] is False
    assert not scope["implementation_authorized"] and not scope["compiler_authorized"]
    assert scope["hard_total_source_line_stop"] == 250
    assert scope["reduced_source_estimate"] == [145, 210]
    assert history["original_budget_intervals_sum"] == [215, 265]
    assert history["original_claimed_upper_target"] == 250 and not history["budget_claim_correct"]
    assert history["source_jobs"] == 0
    for name, expected in history["files"].items():
        assert sha(HERE / relative(name)) == expected
        assert (HERE / relative(name)).read_bytes() == (HERE / "original-three-head-proposal" / relative(name)).read_bytes()
    original = (HERE / "proposed-signatures.lean.txt").read_bytes()
    chosen = (HERE / "selected-signatures.lean.txt").read_bytes()
    assert chosen == original.split(b"theorem stage_bounds", 1)[0]
    assert len(chosen.splitlines()) == selected["selected_header_lines"] == 8
    assert chosen.count(b"noncomputable def ") == chosen.count(b"theorem ") == 1
    assert b"stage_bounds" not in chosen
    assert sha(HERE / "selected-signatures.lean.txt") == selected["selected_header_sha256"] == "25af429aaa28afb3dab6c396ca47460c4cc72561128611f34d8567ac8bc37e6f"
    assert sha(HERE / "equations.md") == selected["equations_sha256"] == "96866d92a9c40e4cf81654e0bef04bfb5a1eccaf74a72eb0cc34a1659f1d28a1"
    assert sha(HERE / "selected-plan.md") == selected["selected_plan_sha256"]
    assert sha(HERE / "report.md") == selected["report_sha256"]
    assert not list(HERE.glob("*.lean")) and not list(HERE.rglob("*.olean"))
    assert not list(HERE.rglob("*.log"))
    print(json.dumps(dict(status="PASS", live=args.live, local_pins=len(manifest["files"]), root_pins=6,
        toolchain_pins=4, source_ranges=19, proof_jobs=0, runtime_jobs=0, canonical_jobs=0,
        selected_public_heads=selected["selected_public_heads"], envelope_defined=False,
        retention_proved=False, stage_bounds_proved=False, adequacy_proved=False,
        manifest_sha256=sha(HERE / "manifest.json")), indent=2))

if __name__ == "__main__":
    main()
