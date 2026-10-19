#!/usr/bin/env python3
"""Verify the explicit source-review pins without running Lean."""

from hashlib import sha256
import json
from pathlib import Path


def main() -> None:
    script = Path(__file__).resolve()
    root = script.parents[3]
    manifest = script.with_name("recursive-audit-v2-pins.json")
    record = json.loads(manifest.read_text())
    for entry in record["pins"]:
        target = root / entry["path"]
        data = target.read_bytes()
        assert len(data) == entry["bytes"], entry["path"]
        assert sha256(data).hexdigest() == entry["sha256"], entry["path"]
    print(json.dumps({
        "pass": True,
        "pins": len(record["pins"]),
        "manifest_sha256": sha256(manifest.read_bytes()).hexdigest(),
        "owned_lean_runs": 0,
        "owned_proof_pairs": 0,
    }, indent=2))


if __name__ == "__main__":
    main()
