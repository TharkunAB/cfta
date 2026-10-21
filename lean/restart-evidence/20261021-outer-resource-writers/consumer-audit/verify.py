#!/usr/bin/env python3
"""Verify the source-only resource-writer consumer audit."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def relative(text: str) -> Path:
    path = Path(text)
    assert not path.is_absolute() and ".." not in path.parts, text
    return path


def check(path: Path, pin: dict) -> None:
    data = path.read_bytes()
    assert len(data) == pin["bytes"] and sha(data) == pin["sha256"], str(path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text())
    assert manifest["finalized"] and manifest["source_only"]
    assert manifest["owned_lean_lake_commands"] == manifest["new_public_pairs"] == 0
    assert manifest["implementation_proved"] is False
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
    proposal = (HERE / "proposed-signature.lean.txt").read_text()
    assert re.findall(r"^theorem (\w+)", proposal, re.M) == ["key_ne_top"]
    assert "namespace MicroCFTA.SourceCurrentResourceOwnerProgress" in proposal
    assert proposal.count("(written : Written (bits := bits) formulas solver request returned)") == 1
    for token in ("member : request.value ∈ ownerRows", "returned.children[index]?",
                  "run returned.entry.key.constraint", "combined ≠ .contradiction",
                  "laterGrowth : Grows", "top : EqReady prefixBefore.constraints (.live identity [])",
                  "returned.entry.key.constraint = request.value.entry.key.constraint",
                  "child.1.payload ≠ some []"):
        assert token in proposal, token
    assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b| := by", proposal)
    assert not any(token in proposal for token in ("OuterParentHistory.Written", "Rel ", "Covers ", "pair :", "HistoricalSupport"))
    writers = (HERE / "inputs/root/lean/MicroCFTA/SourceCurrentResourceParentWriters.lean").read_text()
    assert sha(writers.encode()) == "404f9ba2b58cbdb403608465e375d6f1af66686aaa3201288ba6ea219f75f4d2"
    assert "def Written" in writers and "residentReserved bits budget request writerBefore.checked profile" in writers
    certificates = (HERE / "inputs/root/lean/MicroCFTA/SourceCurrentActualParentSelectedCertificates.lean").read_text()
    assert "theorem selected_certificates" in certificates
    assert "∃ numeric : SourceCurrentParentNumeric.Receipt" in certificates
    assert "before memos result after savedFourth saved final" in certificates
    report = (HERE / "report.md").read_text()
    for boundary in ("Top-owner exclusion", "No writer-to-reader heap or operation interval",
                     "No current/prepared false gate", "historical writer-entry oracle"):
        assert boundary.lower() in report.lower(), boundary
    print(json.dumps({"status": "PASS", "live": args.live, "source_only": True,
                      "local_pins": len(manifest["files"]), "root_pins": len(pins),
                      "proposed_public_heads": ["MicroCFTA.SourceCurrentResourceOwnerProgress.key_ne_top"],
                      "owned_lean_lake_commands": 0, "new_public_pairs": 0,
                      "implementation_proved": False,
                      "manifest_sha256": sha((HERE / "manifest.json").read_bytes())}, indent=2))


if __name__ == "__main__":
    main()
