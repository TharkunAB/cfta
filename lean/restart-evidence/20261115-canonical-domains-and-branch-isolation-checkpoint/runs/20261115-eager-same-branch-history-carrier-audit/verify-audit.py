from pathlib import Path
import hashlib
import json
import re

packet = Path(__file__).resolve().parent
root = packet.parents[2]
pins = json.loads((packet / "source-pins.json").read_text())
for filename, expected in pins.items():
    assert hashlib.sha256((root / filename).read_bytes()).hexdigest() == expected, filename
entries = json.loads((packet / "header-map.json").read_text())
blocks = re.split(r"^===== [^\n]+ =====\n", (packet / "EXACT-HEADERS.txt").read_text(), flags=re.M)[1:]
assert len(blocks) == len(entries)
for entry, block in zip(entries, blocks):
    fragment = block.rstrip()
    assert hashlib.sha256(fragment.encode()).hexdigest() == entry["fragmentSha256"], entry
    lines = (root / entry["file"]).read_text().splitlines(keepends=True)
    assert "".join(lines[entry["line"] - 1:]).startswith(fragment), entry
original = next(filename for filename in pins if filename.endswith("/RELATION-TARGET.md"))
assert (packet / "PRESERVED-RELATION-TARGET.md").read_bytes() == (root / original).read_bytes()
assert not list(packet.glob("*.lean"))
print(f"STATIC PASS: {len(pins)} source pins, {len(entries)} exact fragments, preserved target bytes; no Lean source added.")
