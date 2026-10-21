#!/usr/bin/env python3
"""Check this source plan. Do not run a proof or evaluate the envelope."""
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
    parser.add_argument("--toolchain-source", type=Path, required=True)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text())
    assert manifest["finalized"] and manifest["source_only"]
    for pin in manifest["files"]:
        check(HERE / relative(pin["path"]), pin)
    data = json.loads((HERE / "source-pins.json").read_text())
    sources = data["sources"]
    index = json.loads((HERE / "source-index.json").read_text())
    assert sources == manifest["sources"] and len(sources) == len(index) == 10
    assert sum(s["authority"] == "root" for s in sources) == 5
    assert sum(s["authority"] == "toolchain" for s in sources) == 5
    assert sum(len(s["reviewed_ranges"]) for s in sources) == 22
    for source, cited in zip(sources, index, strict=True):
        assert all(source[k] == cited[k] for k in ["id", "authority", "path"])
        snapshot = HERE / relative(source["snapshot"])
        check(snapshot, source)
        lines = snapshot.read_bytes().splitlines(keepends=True)
        assert len(lines) == source["lines"]
        assert len(source["reviewed_ranges"]) == len(cited["ranges"])
        for span, (first, last) in zip(source["reviewed_ranges"], cited["ranges"], strict=True):
            assert (span["start"], span["end"]) == (first, last)
            assert 1 <= first <= last <= len(lines)
            block = b"".join(lines[first - 1:last])
            assert hashlib.sha256(block).hexdigest() == span["sha256"]
            expected = "".join(f"{n:5d} {line.decode()}" for n, line in enumerate(lines[first - 1:last], first))
            assert (HERE / relative(span["excerpt"])).read_text() == expected
        if args.live:
            origin = args.root if source["authority"] == "root" else args.toolchain_source
            check(origin / relative(source["path"]), source)
    selected = json.loads((HERE / "selection.json").read_text())
    scope = json.loads((HERE / "scope.json").read_text())
    assert selected == manifest["selection"] and scope == manifest["scope"]
    assert selected["finalized"] and selected["source_only"]
    assert selected["selected_public_heads"] == ["stage_bounds"]
    assert selected["selected_lean_attempts"] == selected["selected_public_attempts"] == []
    for key in ["lean_jobs", "lake_jobs", "canonical_jobs", "runtime_jobs", "public_pairs", "constructed_pairs", "board_jobs", "official_edits"]:
        assert selected[key] == 0
    for key in ["stage_bounds_proved", "physical_adequacy_proved", "adequate_outer_fuel_proved", "capacity_resolved"]:
        assert selected[key] is False
    assert selected["checked_envelope_defined"] and selected["checked_entry_retention_proved"]
    assert scope["hard_total_source_line_stop"] == 250 and scope["source_estimate"] == [225, 250]
    assert scope["table_extrema"] == [220, 250]
    assert not scope["implementation_authorized"] and not scope["compiler_authorized"]
    original = (HERE / "historical/original-42-line-proposal.lean.txt").read_bytes()
    header = (HERE / "proposed-signature.lean.txt").read_bytes()
    assert len(original.splitlines()) == 42 and len(header.splitlines()) == 34
    assert header == b"theorem stage_bounds " + original.split(b"theorem stage_bounds ", 1)[1]
    assert header.count(b"theorem ") == 1 and b"def " not in header
    assert sha(HERE / "proposed-signature.lean.txt") == selected["header_sha256"] == "473b65048b665c273877a1a38f73dce6f2f63001abcd7a40ce79ad86b534293e"
    for key, name in [("plan_sha256", "plan.md"), ("report_sha256", "report.md"), ("unfold_route_sha256", "one-rank-unfold.md"), ("budget_sha256", "source-budget.md"), ("clarifications_sha256", "proof-route-clarifications.md")]:
        assert sha(HERE / name) == selected[key]
    assert sources[0]["sha256"] == selected["checked_dependency_sha256"] == "b8401732ae63be4d2036ccd4af7997b787ced8787789a1fb9d2e354047fde5ba"
    assert sources[0]["lines"] == 157
    dependency = json.loads((HERE / "checked-dependency/owner-selection.json").read_text())
    assert dependency["finalized"] and dependency["source_sha256"] == sources[0]["sha256"]
    assert dependency["actual_lean_jobs"] == 5 and dependency["failed_jobs"] == 3
    assert dependency["stage_bounds_proved"] is False and dependency["entry_retention_proved"]
    cue = json.loads((HERE / "checked-dependency/root-verification-cue.json").read_text())
    assert cue["source_sha256"] == sources[0]["sha256"]
    assert cue["root_reported_strict_exit"] == cue["root_reported_audit_exit"] == 0
    assert cue["root_reported_audit_jobs"] == 3616 and cue["root_reported_audit_dependencies"] == 75112
    assert cue["new_jobs_from_recording_cue"] == 0
    assert not list(HERE.glob("*.lean")) and not list(HERE.rglob("*.olean"))
    assert not list(HERE.rglob("*.log"))
    print(json.dumps(dict(status="PASS", live=args.live, local_pins=len(manifest["files"]), root_pins=5,
        toolchain_pins=5, source_ranges=22, proof_jobs=0, runtime_jobs=0, canonical_jobs=0,
        selected_public_heads=["stage_bounds"], stage_bounds_proved=False,
        implementation_authorized=False, compiler_authorized=False,
        manifest_sha256=sha(HERE / "manifest.json")), indent=2))


if __name__ == "__main__":
    main()
