#!/usr/bin/env python3
"""Verify the immutable reader survey inputs and exact source header excerpts."""
from pathlib import Path
import hashlib
import json
import re
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
manifest=json.loads((HERE/"next-reader-survey-manifest.json").read_text())
assert len(manifest["entries"])==manifest["entry_count"]
seen=set()
for entry in manifest["entries"]:
    relative=entry["path"]
    assert relative not in seen,relative
    seen.add(relative)
    assert relative.startswith("lean/MicroCFTA/") or relative.startswith(str(HERE.relative_to(ROOT))+"/next-reader-")
    data=(ROOT/relative).read_bytes()
    assert len(data)==entry["bytes"],relative
    assert hashlib.sha256(data).hexdigest()==entry["sha256"],relative
headers=(HERE/"next-reader-header-excerpts.md").read_text()
blocks=re.findall(r"`(lean/MicroCFTA/[^`]+):(\d+)`\n\n```lean\n(.*?)\n```",headers,re.S)
index=json.loads((HERE/"next-reader-header-index.json").read_text())
assert len(blocks)==len(index)==75
assert len({path for path,_line,_header in blocks})==18
for (path,line,header),entry in zip(blocks,index):
    assert entry["path"]==path and entry["line"]==int(line)
    assert hashlib.sha256(header.encode()).hexdigest()==entry["header_sha256"]
    tail="\n".join((ROOT/path).read_text().splitlines()[int(line)-1:])
    assert tail.startswith(header),(path,line)
for path in [HERE/"next-reader-survey.md",HERE/"next-reader-header-excerpts.md"]:
    data=path.read_bytes()
    assert data.endswith(b"\n") and not data.endswith(b"\n\n"),path
print(f"PASS: {manifest['entry_count']} hashes; 18 immutable production inputs; 75 exact source headers; no build")
