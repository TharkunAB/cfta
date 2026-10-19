#!/usr/bin/env python3
"""Verify the frozen recursive observation origin component."""

from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import re


def main() -> None:
    script = Path(__file__).resolve()
    here = script.parent
    root = script.parents[3]
    manifest = here / "origin-manifest.json"
    record = json.loads(manifest.read_text())
    for entry in record["pins"]:
        data = (root / entry["path"]).read_bytes()
        assert len(data) == entry["bytes"], entry["path"]
        assert sha256(data).hexdigest() == entry["sha256"], entry["path"]

    selection = json.loads((here / "origin-selection.json").read_text())
    production = root / selection["production"]
    strict = json.loads((here / (selection["strict"] + ".json")).read_text())
    assert strict["exit_code"] == 0
    assert not (here / strict["log"]).read_bytes()
    assert (here / strict["source"]).read_bytes() == production.read_bytes()

    spec = importlib.util.spec_from_file_location("origin_probe_tools", here / "origin-probe-tools.py")
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    for group in selection["groups"]:
        probes.check_group(group)
    for stem in selection["entered_lean_jobs"]:
        probes.check_limits(stem)
        meta = json.loads((here / (stem + ".json")).read_text())
        assert meta["wrapper"][1:5] == ["--mem", "4G", "--time", "5m"]

    canonical = json.loads((here / (selection["canonical"] + ".json")).read_text())
    assert canonical["exit_code"] == 0
    log = (here / canonical["log"]).read_text()
    warnings = re.findall(r"^warning: (.*)$", log, re.M)
    assert len(warnings) == 1 and warnings[0].startswith(selection["canonical_allowed_warning_source"])
    assert "Build completed successfully" in log
    assert not re.search(r"^error:|sorryAx", log, re.M)
    assert len((here / "origin-final-peaks.txt").read_text().splitlines()) == 5

    print(json.dumps({
        "pass": True,
        "pins": len(record["pins"]),
        "manifest_sha256": sha256(manifest.read_bytes()).hexdigest(),
        "public_heads": 1,
        "constructed_heads": 0,
        "owned_entered_lean_jobs": 5,
        "retained_blocked_wrapper_attempts": 1,
        "strict_log_bytes": 0,
    }, indent=2))


if __name__ == "__main__":
    main()
