#!/usr/bin/env python3
"""Verify retained documentation ranges and immutable review pins."""

from hashlib import sha256
import json
from pathlib import Path


def main() -> None:
    script = Path(__file__).resolve()
    root = script.parents[3]
    manifest = script.with_name("plain-doc-pins.json")
    record = json.loads(manifest.read_text())
    for entry in record["pins"]:
        data = (root / entry["path"]).read_bytes()
        assert len(data) == entry["bytes"], entry["path"]
        assert sha256(data).hexdigest() == entry["sha256"], entry["path"]

    snapshot = json.loads(script.with_name("plain-doc-ranges.json").read_text())
    assert len(snapshot["ranges"]) == 12
    for entry in snapshot["ranges"]:
        text = entry["text"]
        assert sha256(text.encode()).hexdigest() == entry["sha256"], entry["path"]
        lines = (root / entry["path"]).read_text().splitlines(keepends=True)
        current = "".join(lines[entry["start_line"] - 1:entry["end_line"]])
        assert current == text, (entry["path"], entry["start_line"])
    assert len({entry["sha256"] for entry in snapshot["ranges"][:7]}) == 1

    print(json.dumps({
        "pass": True,
        "pins": len(record["pins"]),
        "ranges": len(snapshot["ranges"]),
        "identical_status_blocks": 7,
        "manifest_sha256": sha256(manifest.read_bytes()).hexdigest(),
        "owned_lean_runs": 0,
        "owned_proof_pairs": 0,
    }, indent=2))


if __name__ == "__main__":
    main()
