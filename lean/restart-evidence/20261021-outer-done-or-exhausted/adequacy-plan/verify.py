#!/usr/bin/env python3
"""Check the adequacy survey snapshots without running a proof or arithmetic model."""
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
    args = parser.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text())
    assert manifest["finalized"] and manifest["source_only"]
    for pin in manifest["files"]:
        check(HERE / relative(pin["path"]), pin)
    sources = json.loads((HERE / "source-pins.json").read_text())["sources"]
    index = json.loads((HERE / "source-index.json").read_text())
    assert sources == manifest["sources"] and len(sources) == len(index) == 10
    assert sum(len(source["reviewed_ranges"]) for source in sources) == 20
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
    selected = json.loads((HERE / "selection.json").read_text())
    assert scope == manifest["scope"] and selected == manifest["selection"]
    assert selected["source_only"] and selected["status"] == "undefined_unproved_numeric_design"
    assert selected["proposed_public_heads"] == selected["selected_lean_attempts"] == selected["selected_public_attempts"] == []
    for key in ["lean_jobs", "lake_jobs", "canonical_jobs", "runtime_jobs", "public_pairs", "constructed_pairs", "official_edits"]:
        assert selected[key] == 0
    for key in ["C_defined", "F_constructed", "adequacy_proved", "capacity_resolved", "state_widening_proved"]:
        assert selected[key] is False
    assert not scope["implementation_authorized"] and scope["proof_jobs"] == scope["runtime_jobs"] == scope["canonical_jobs"] == scope["official_edits"] == 0
    assert scope["proposed_public_head"] is None
    assert len((HERE / "plan.md").read_text().splitlines()) == selected["plan_lines"] == 40
    assert len((HERE / "candidate-contract.md").read_text().splitlines()) == selected["candidate_lines"] == 24
    assert sha(HERE / "plan.md") == selected["plan_sha256"] == "0327c32d4536186c0ed6722e1866c7635b578a96bcb148b93457adb4805eb92c"
    assert sha(HERE / "candidate-contract.md") == selected["candidate_contract_sha256"] == "585feac191bd225109ae0f78eadba1f3335f1569524469a0870b124a666c692f"
    assert sha(HERE / "report.md") == selected["report_sha256"] == "2e078a04b1c8062e37a98c71d12e27a74071c43d818c05df21ac76906c3648cf"
    assert not list(HERE.glob("*.lean")) and not list(HERE.glob("*.olean")) and not list(HERE.glob("*.log"))
    assert not list(HERE.glob("proposed-signature*"))
    print(json.dumps(dict(status="PASS", live=args.live, local_pins=len(manifest["files"]), root_pins=10, source_ranges=20, proof_jobs=0, runtime_jobs=0, canonical_jobs=0, C_defined=False, F_constructed=False, adequacy_proved=False, proposed_public_heads=[], manifest_sha256=sha(HERE / "manifest.json")), indent=2))

if __name__ == "__main__":
    main()
