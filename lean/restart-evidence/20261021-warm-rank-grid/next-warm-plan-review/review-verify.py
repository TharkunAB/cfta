#!/usr/bin/env python3
"""Verify the source-only warm packet plan review."""
from pathlib import Path
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent

def digest(data):
    return hashlib.sha256(data).hexdigest()

def check(condition, message):
    if not condition:
        raise SystemExit(message)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((HERE / "review-manifest.json").read_text())
    for entry in manifest["local_files"]:
        data = (HERE / entry["path"]).read_bytes()
        check(digest(data) == entry["sha256"], "local hash: " + entry["path"])
        check(len(data) == entry["bytes"], "local length: " + entry["path"])
    selected = HERE / "reviewed-proposal-initial"
    index = json.loads((selected / "source-index.json").read_text())
    sources = {entry["path"]: entry for entry in index["sources"]}
    ranges = set()
    for entry in index["sources"]:
        data = (selected / entry["snapshot"]).read_bytes()
        check(digest(data) == entry["sha256"], "source snapshot: " + entry["path"])
        check(len(data) == entry["bytes"], "source length: " + entry["path"])
        if args.live:
            check((args.root / entry["path"]).read_bytes() == data, "live source: " + entry["path"])
        lines = data.splitlines(keepends=True)
        for scope in entry["reviewed_ranges"]:
            check(1 <= scope["start"] <= scope["end"] <= len(lines), "range bounds")
            excerpt = b"".join(lines[scope["start"] - 1:scope["end"]])
            check(digest(excerpt) == scope["sha256"], "range hash: " + scope["excerpt"])
            check(excerpt == (selected / scope["excerpt"]).read_bytes(), "range snapshot")
            ranges.add((entry["path"], scope["start"], scope["end"]))
    for scope in json.loads((HERE / "additional-reviewed-ranges.json").read_text()):
        entry = sources[scope["path"]]
        check(entry["sha256"] == scope["source_sha256"], "additional source hash")
        lines = (selected / entry["snapshot"]).read_bytes().splitlines(keepends=True)
        excerpt = b"".join(lines[scope["start"] - 1:scope["end"]])
        check(digest(excerpt) == scope["sha256"], "additional range hash")
        check(excerpt == (HERE / scope["excerpt"]).read_bytes(), "additional snapshot")
        ranges.add((scope["path"], scope["start"], scope["end"]))
    check(len(sources) == 20 and len(ranges) == 26, "review inventory counts")
    status = json.loads((HERE / "review-status.json").read_text())
    check(all(status[key] == 0 for key in ("reviewer_compiler_jobs", "reviewer_runtime_jobs", "reviewer_capped_jobs", "official_edits")), "job accounting")
    print(json.dumps({"status": "PASS", "live": args.live, "local_files": len(manifest["local_files"]), "root_sources": len(sources), "distinct_current_ranges": len(ranges), "reviewer_proof_jobs": 0}, sort_keys=True))

if __name__ == "__main__":
    main()
