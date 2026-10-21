#!/usr/bin/env python3
"""Verify the frozen source-only finite warm consumer plan audit."""
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
    parser.add_argument("--toolchain-source", type=Path)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((HERE / "review-manifest.json").read_text())
    for item in manifest["local_files"]:
        data = (HERE / item["path"]).read_bytes()
        assert sha(data) == item["sha256"] and len(data) == item["bytes"], item["path"]
    proposal = HERE / "reviewed-proposal"
    index = json.loads((proposal / "source-index.json").read_text())
    roots = external = scopes = 0
    for item in index["sources"]:
        data = (proposal / item["snapshot"]).read_bytes()
        assert sha(data) == item["sha256"] and len(data.splitlines()) == item["splitlines"]
        if "root_path" in item:
            roots += 1
            live = args.root / item["root_path"]
        else:
            external += 1
            if args.live:
                assert args.toolchain_source is not None, "pass --toolchain-source for live toolchain checks"
                relative = item["toolchain_path"].split("/src/lean/", 1)[1]
                live = args.toolchain_source / relative
        if args.live:
            assert live.read_bytes() == data
        lines = data.splitlines(keepends=True)
        for scope in item["ranges"]:
            assert 1 <= scope["start"] <= scope["end"] <= len(lines)
            excerpt = b"".join(lines[scope["start"] - 1:scope["end"]])
            assert sha(excerpt) == scope["sha256"] and excerpt == (proposal / scope["snapshot"]).read_bytes()
            scopes += 1
    old = (proposal / "original-empty-inherited-draft/proposed-signature.lean.txt").read_bytes()
    new = (proposal / "proposed-signature.lean.txt").read_bytes()
    removed = b"      (emptyPayload : inherited.payload = some [])\n"
    assert old.count(removed) == 1 and old.replace(removed, b"", 1) == new
    assert sha(new) == "1db917531492f0f7972d03c5dc35ff575112d7bd24dfc9fd3bb8baca5f7071bd"
    assert (roots, external, scopes) == (20, 1, 26)
    print(json.dumps({"status": "PASS", "live": args.live, "local_files": len(manifest["local_files"]), "root_sources": roots, "toolchain_sources": external, "strict_ranges": scopes, "reviewer_proof_jobs": 0}, sort_keys=True))

if __name__ == "__main__":
    main()
