#!/usr/bin/env python3
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parents[3]
manifest = json.loads(Path(__file__).with_name("node-origin-manifest.json").read_text())
for entry in manifest["entries"]:
    path = root / entry["path"]
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    assert actual == entry["sha256"], entry["path"]
log = Path(__file__).with_name("node-origin-search-2.log").read_text()
assert "(3651,Stats {calls = 30669, hits = 11788, maximumActive = 8})" in log
assert "CANDIDATE" not in log
cold = Path(__file__).with_name("node-origin-cold-1.log").read_text()
assert cold.count("case=") == 8
assert cold.count("(1,Stats") == 8
for name in ["node-origin-search-2.json", "node-origin-cold-1.json"]:
    assert json.loads(Path(__file__).with_name(name).read_text())["exit"] == 0
print(f"PASS {len(manifest['entries'])} entries; 3651 cases and 8 selected node-cold checks")
