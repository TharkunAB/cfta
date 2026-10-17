#!/usr/bin/env python3
"""Verify exact source excerpts and frozen read-only comparison survey bytes."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main() -> None:
    headers = json.loads((HERE / "next-comparison-headers.json").read_text())
    assert len(headers) == 48
    sources = {entry["source"] for entry in headers}
    assert len(sources) == 19
    for entry in headers:
        path = ROOT / entry["source"]
        assert sha(path) == entry["sha256"], entry["source"]
        lines = path.read_text().splitlines()
        assert "\n".join(lines[entry["first_line"] - 1:entry["last_line"]]) + "\n" == entry["text"], entry["declaration"]
    print("PASS 48 exact declaration excerpts from 19 immutable production sources")
    survey = (HERE / "next-comparison-survey.md").read_text()
    for required in ["proposed, not proved", "heap-equal unfold events as stutters", "does not require the whole captured forest closed", "No new Haskell behavior defect"]:
        assert required in survey, required
    print("PASS proposed-stage/stuttering and selected-open-forest scope are explicit")
    if "--checks-only" not in sys.argv:
        manifest = json.loads((HERE / "next-comparison-manifest.json").read_text())
        assert manifest["file_count"] == len(manifest["files"])
        for entry in manifest["files"]:
            path = ROOT / entry["path"]
            assert path.stat().st_size == entry["bytes"], entry["path"]
            assert sha(path) == entry["sha256"], entry["path"]
        print(f"PASS {manifest['file_count']} frozen hashes and byte counts")

if __name__ == "__main__":
    main()
