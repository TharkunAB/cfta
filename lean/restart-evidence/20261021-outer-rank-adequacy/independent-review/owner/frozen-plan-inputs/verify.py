#!/usr/bin/env python3
"""Verify the portable plan and its optional current repository sources."""
from pathlib import Path
import argparse
import hashlib
import json
import re


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / "manifest.json").read_text())
    for item in manifest["files"]:
        data = (here / item["path"]).read_bytes()
        assert len(data) == item["bytes"], item["path"]
        assert digest(data) == item["sha256"], item["path"]
    index = json.loads((here / "source-index.json").read_text())
    snapshots = json.loads((here / "snapshots.json").read_text())
    assert len(index["sources"]) == len(snapshots["sources"]) == 24
    count = 0
    for original, saved in zip(index["sources"], snapshots["sources"], strict=True):
        assert original["path"] == saved["root_path"]
        data = (here / saved["snapshot"]).read_bytes()
        assert digest(data) == original["sha256"], saved["snapshot"]
        lines = data.splitlines(keepends=True)
        assert len(original["ranges"]) == len(saved["ranges"])
        for span, recorded in zip(original["ranges"], saved["ranges"], strict=True):
            assert 1 <= span["start_line"] <= span["end_line"] <= len(lines)
            selected = b"".join(lines[span["start_line"] - 1:span["end_line"]])
            assert digest(selected) == span["sha256"], saved["snapshot"]
            assert (here / recorded["snapshot"]).read_bytes() == selected
            count += 1
        if args.live:
            current = args.root / original["path"]
            assert digest(current.read_bytes()) == original["sha256"], str(current)
    assert count == 32
    selection = json.loads((here / "selection.json").read_text())
    assert selection["implementation_authorized"] is False
    assert selection["compiler_authorized"] is False
    assert selection["new_proof_or_runtime_jobs"] == 0
    assert selection["approved_hard_stop_total_lines"] == 650
    header = (here / "proposed-signature.lean.txt").read_text()
    assert re.findall(r"^theorem (\w+)", header, re.MULTILINE) == ["initial_node_call"]
    assert len(header.splitlines()) == 36
    assert len((here / "plan.md").read_text().splitlines()) == 35
    assert len((here / "context.lean.txt").read_text().splitlines()) == 21
    print(json.dumps({"status": "PASS", "live": args.live,
        "local_pins": len(manifest["files"]), "root_sources": 24,
        "ranges": count, "public_headers": 1,
        "new_proof_or_runtime_jobs": 0}, sort_keys=True))


if __name__ == "__main__":
    main()
