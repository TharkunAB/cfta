#!/usr/bin/env python3
"""Verify the frozen source-only warm packet review."""
from pathlib import Path
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((HERE / "review-manifest.json").read_text())
    for item in manifest["local_files"]:
        data = (HERE / item["path"]).read_bytes()
        assert sha(data) == item["sha256"], item["path"]
        assert len(data) == item["bytes"], item["path"]
    index = json.loads((HERE / "reference-source-index.json").read_text())
    scopes = 0
    for item in index["sources"]:
        data = (HERE / item["snapshot"]).read_bytes()
        assert sha(data) == item["sha256"] and len(data) == item["bytes"]
        if args.live:
            assert (args.root / item["path"]).read_bytes() == data, item["path"]
        lines = data.splitlines(keepends=True)
        for scope in item["reviewed_ranges"]:
            assert 1 <= scope["start"] <= scope["end"] <= len(lines)
            excerpt = b"".join(lines[scope["start"] - 1:scope["end"]])
            assert sha(excerpt) == scope["sha256"]
            assert excerpt == (HERE / scope["excerpt"]).read_bytes()
            scopes += 1
    source = (HERE / "SourceCurrentWarmNextPacket.reviewed.lean.txt").read_bytes()
    assert sha(source) == "13e8373cff925aca8832a47e12514767dd94dbe3fdb8d68bd73b2cdf19246be8"
    assert len(source.splitlines()) == 117
    header = b"theorem node_call\n" + source.split(b"theorem node_call\n", 1)[1].split(b"\n := by\n", 1)[0] + b"\n"
    assert header == (HERE / "reference-proposed-signature.lean.txt").read_bytes()
    assert source.startswith((HERE / "reference-proposed-context.lean.txt").read_bytes())
    assert len(index["sources"]) == 20 and scopes == 24
    print(json.dumps({"status": "PASS", "live": args.live, "local_files": len(manifest["local_files"]), "root_sources": 20, "ranges": scopes, "source_lines": 117, "reviewer_proof_jobs": 0}, sort_keys=True))

if __name__ == "__main__":
    main()
