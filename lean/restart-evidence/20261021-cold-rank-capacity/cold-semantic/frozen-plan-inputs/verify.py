"""Verify source-only plan pins without compiling or evaluating C."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json

HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument("--root", type=Path, required=True)
parser.add_argument("--live", action="store_true")
args = parser.parse_args()
digest = lambda data: hashlib.sha256(data).hexdigest()
manifest = json.loads((HERE / "manifest.json").read_text())
selected = json.loads((HERE / "selection.json").read_text())
assert manifest["finalized"] and selected["finalized"]
for pin in manifest["files"]:
    path = Path(pin["path"])
    assert not path.is_absolute() and ".." not in path.parts
    data = (HERE / path).read_bytes()
    assert len(data) == pin["bytes"] and digest(data) == pin["sha256"], pin["path"]
index = json.loads((HERE / "source-index.json").read_text())
for pin in index["sources"]:
    data = (HERE / pin["snapshot"]).read_bytes()
    assert len(data) == pin["bytes"] and digest(data) == pin["sha256"]
    lines = data.splitlines(True)
    assert len(lines) == pin["lines"]
    for span in pin["reviewed_ranges"]:
        assert 1 <= span["start"] <= span["end"] <= len(lines)
        part = b"".join(lines[span["start"] - 1:span["end"]])
        assert len(part) == span["bytes"] and digest(part) == span["sha256"]
        assert part == (HERE / span["excerpt"]).read_bytes()
    if args.live:
        assert (args.root / pin["path"]).read_bytes() == data
old = (HERE / "history/original-context-15.lean.txt").read_text()
new = (HERE / "context.lean.txt").read_text()
assert new == old.replace("open Cache InternedConstructorTemplates\n", "open Cache InternedConstructorTemplates InternedProbeProvenance\n", 1)
assert "".join(difflib.unified_diff(old.splitlines(True), new.splitlines(True), fromfile="original-context-15.lean.txt", tofile="context.lean.txt")) == (HERE / "context-available.patch").read_text()
header = (HERE / "proposed-signature.lean.txt").read_bytes()
assert len(header.splitlines()) == 30 and digest(header) == selected["header_sha256"]
producer = index["pending_producer"]
assert digest((HERE / producer["snapshot"]).read_bytes()) == producer["sha256"]
assert digest((HERE / producer["header"]).read_bytes()) == producer["header_sha256"]
assert selected["new_lean_jobs"] == selected["new_runtime_jobs"] == 0
assert not selected["semantic_corollary_proved"] and not selected["compiler_authorized"]
print(json.dumps(dict(status="PASS", live=args.live, local_pins=len(manifest["files"]), root_pins=len(index["sources"]), source_ranges=sum(len(p["reviewed_ranges"]) for p in index["sources"]), public_heads=1, new_lean_jobs=0, new_runtime_jobs=0, semantic_corollary_proved=False), indent=2))
