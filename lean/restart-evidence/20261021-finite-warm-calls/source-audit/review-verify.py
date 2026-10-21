#!/usr/bin/env python3
"""Verify the frozen source-only finite warm calls implementation audit."""
from pathlib import Path
import argparse
import difflib
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
    index = json.loads((HERE / "source-index.json").read_text())
    roots = tools = scopes = 0
    for item in index["sources"]:
        data = (HERE / item["snapshot"]).read_bytes()
        assert sha(data) == item["sha256"] and len(data.splitlines()) == item["splitlines"]
        if "root_path" in item:
            roots += 1
            live = args.root / item["root_path"]
        else:
            tools += 1
            if args.live:
                assert args.toolchain_source is not None, "pass --toolchain-source"
                live = args.toolchain_source / item["toolchain_relative"]
        if args.live:
            assert live.read_bytes() == data, item
        lines = data.splitlines(keepends=True)
        for scope in item["ranges"]:
            assert 1 <= scope["start"] <= scope["end"] <= len(lines)
            excerpt = b"".join(lines[scope["start"] - 1:scope["end"]])
            assert sha(excerpt) == scope["sha256"]
            assert excerpt == (HERE / scope["snapshot"]).read_bytes()
            scopes += 1
    owner = HERE / "reviewed-author"
    old = (owner / "initial-complete-210.source.lean.txt").read_bytes()
    new = (owner / "SourceCurrentFiniteWarmCalls.lean").read_bytes()
    assert sha(old) == "3539730b7bf2782860da21ec5f706f8868e80d7b4936c718caadbe6a269857d0"
    assert sha(new) == "32cfa9e1a229237dcaf683fe77f588cb2eeb541929f7e4dff33ef2809370183c"
    assert new == (owner / "amended-complete-236.source.lean.txt").read_bytes()
    expected = "".join(difflib.unified_diff(old.decode().splitlines(keepends=True),
        new.decode().splitlines(keepends=True), fromfile="initial-complete-210.source.lean.txt",
        tofile="amended-complete-236.source.lean.txt")).encode()
    assert expected == (owner / "prelaunch-semantic-amendment.patch").read_bytes()
    start = new.index(b"theorem node_calls\n")
    header = new[start:new.index(b" := by", start)]
    assert header == (owner / "amended-proposed-signature.lean.txt").read_bytes()
    assert sha(header) == "f064b85a8c47b33fa3a2a2328654aca227e5b91d0bf05472510054750517ccaa"
    context = (owner / "frozen-plan-inputs/proposed-context.lean.txt").read_bytes()
    assert new.startswith(context)
    entry = lambda data: data[data.index(b"private def Entry"):data.index(b"private theorem advance_entry")]
    assert entry(old) == entry(new)
    old_start = old.index(b"theorem node_calls\n")
    assert old[old_start:old.index(b" := by", old_start)] == (owner / "frozen-plan-inputs/proposed-signature.lean.txt").read_bytes()
    assert len(new.splitlines()) == 236 < 300 and b"set_option" not in new
    assert (roots, tools, scopes) == (23, 1, 30)
    print(json.dumps({"status": "PASS", "live": args.live,
        "local_files": len(manifest["local_files"]), "root_sources": roots,
        "toolchain_sources": tools, "author_ranges": 29,
        "additional_Fin_last_range": 1, "strict_ranges": scopes,
        "source_review_only": True, "reviewer_proof_jobs": 0}, sort_keys=True))

if __name__ == "__main__":
    main()
