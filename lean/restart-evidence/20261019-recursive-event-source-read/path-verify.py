#!/usr/bin/env python3
"""Check the fixed path-origin source, receipts and complete public probe."""
from __future__ import annotations

import hashlib
import importlib.util
import json
import re
from pathlib import Path


def main() -> None:
    here = Path(__file__).resolve().parent
    root = here.parents[2]
    manifest = json.loads((here / "path-manifest.json").read_text())
    for entry in manifest["files"]:
        data = (root / entry["path"]).read_bytes()
        assert len(data) == entry["bytes"], entry["path"]
        assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]
    selection = json.loads((here / "path-selection.json").read_text())
    spec = importlib.util.spec_from_file_location("path_probe", here / "path-probe-tools.py")
    assert spec is not None and spec.loader is not None
    probe = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probe)
    for stem in selection["attempts"]:
        probe.check_limits(stem)
    strict = selection["strict"]
    meta = json.loads((here / (strict + ".json")).read_text())
    assert meta["exit_code"] == 0
    assert not (here / meta["log"]).read_bytes()
    assert (here / meta["source"]).read_bytes() == (root / selection["source"]).read_bytes()
    canonical = selection["canonical"]
    meta = json.loads((here / (canonical + ".json")).read_text())
    assert meta["exit_code"] == 0
    log = (here / meta["log"]).read_text()
    assert "Build completed successfully (1481 jobs)." in log
    assert not re.search(r"^error:|sorryAx", log, re.M)
    warnings = re.findall(r"^warning:.*$", log, re.M)
    assert len(warnings) == 1 and "InternedFreshOrdinaryClosedCompletion.lean:24:5" in warnings[0]
    for group in selection["groups"]:
        probe.check_group(group)
    assert len((here / "path-final-peaks.txt").read_text().splitlines()) == 5
    print(json.dumps({"status": "PASS", "pins": len(manifest["files"]),
                      "public_heads": 3, "constructed_heads": 0, "lean_jobs": 5,
                      "strict_log_bytes": 0, "canonical_dependency_warnings": 1}))


if __name__ == "__main__":
    main()
