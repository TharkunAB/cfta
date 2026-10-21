"""Verify the portable source-only assessment and mandatory live identities."""
from pathlib import Path
import argparse
import hashlib
import json

def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def relative(name: str) -> Path:
    path = Path(name)
    assert not path.is_absolute() and ".." not in path.parts, name
    return path

parser = argparse.ArgumentParser()
parser.add_argument("--root", type=Path, required=True)
parser.add_argument("--adequacy-header", type=Path, required=True)
parser.add_argument("--capacity-note", type=Path, required=True)
parser.add_argument("--live", action="store_true")
args = parser.parse_args()
here = Path(__file__).resolve().parent
manifest = json.loads((here / "manifest.json").read_text())
selection = json.loads((here / "selection.json").read_text())
assert manifest["finalized"] and selection["finalized"]
for pin in manifest["files"]:
    data = (here / relative(pin["path"])).read_bytes()
    assert len(data) == pin["bytes"] and digest(data) == pin["sha256"], pin["path"]
index = json.loads((here / "source-index.json").read_text())
pins = json.loads((here / "source-pins.json").read_text())["sources"]
assert len(pins) == len(index["sources"]) == 20
for item, pin in zip(index["sources"], pins):
    data = (here / relative(pin["snapshot"])).read_bytes()
    assert len(data) == pin["bytes"] and digest(data) == pin["sha256"] == item["sha256"]
    lines = data.splitlines(keepends=True)
    assert len(lines) == pin["lines"] == item["lines"]
    for span in item.get("ranges", []):
        assert 1 <= span["start"] <= span["end"] <= len(lines), item
        assert digest(b"".join(lines[span["start"] - 1:span["end"]])) == span["sha256"]
    for span in pin["ranges"]:
        first, last = span["start"], span["end"]
        assert 1 <= first <= last <= len(lines), pin
        assert digest(b"".join(lines[first - 1:last])) == span["sha256"]
        excerpt = "".join(f"{n:5d} {line.decode()}" for n, line in enumerate(lines[first - 1:last], first))
        assert (here / relative(span["excerpt"])).read_text() == excerpt
    if args.live:
        if pin["authority"] == "root":
            current = args.root / relative(pin["path"])
        elif pin["authority"] == "adequacy_header":
            current = args.adequacy_header
        else:
            assert pin["authority"] == "capacity_note"
            current = args.capacity_note
        assert digest(current.read_bytes()) == pin["sha256"], str(current)
old = (here / "history/source-index-before-range-correction.json").read_bytes()
new = (here / "source-index.json").read_bytes()
assert old.count(b'"end": 145') == 1
assert new == old.replace(b'"end": 145', b'"end": 144', 1)
assert index["sources"][0]["lines"] == 144
assert index["sources"][0]["ranges"][1]["start"] == 104
assert index["sources"][0]["ranges"][1]["end"] == 144
assert digest((here / "note.md").read_bytes()) == selection["note_sha256"]
assert digest((here / "proposed-signature.lean.txt").read_bytes()) == selection["proposal_sha256"]
assert not selection["implemented"] and not selection["proved"]
assert selection["compiler_or_runtime_jobs"] == 0
print(json.dumps(dict(status="PASS", live=args.live, local_pins=len(manifest["files"]),
    root_sources=18, external_sources=2, source_ranges=sum(len(s["ranges"]) for s in pins),
    strict_bounds_checked_before_slicing=True, source_only=True, new_proof_or_runtime_jobs=0), indent=2))
