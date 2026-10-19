#!/usr/bin/env python3
"""Check the retained current document ranges and their fixed review evidence."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path


def main() -> None:
    here = Path(__file__).resolve().parent
    root = here.parents[2]
    pins = json.loads((here / "source-doc-pins.json").read_text())
    for entry in pins["files"]:
        data = (root / entry["path"]).read_bytes()
        assert len(data) == entry["bytes"], entry["path"]
        assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]
    ranges = json.loads((here / "source-doc-ranges.json").read_text())["ranges"]
    for entry in ranges:
        text = entry["text"]
        assert hashlib.sha256(text.encode()).hexdigest() == entry["sha256"], entry["path"]
        lines = (root / entry["path"]).read_text().splitlines(keepends=True)
        assert "".join(lines[entry["start_line"] - 1 : entry["end_line"]]) == text, entry["path"]
    assert len(ranges) == 13
    assert len({entry["text"] for entry in ranges[:7]}) == 1
    print(json.dumps({"status": "PASS", "pins": len(pins["files"]),
                      "ranges": len(ranges), "new_lean_jobs": 0, "new_proof_pairs": 0}))


if __name__ == "__main__":
    main()
