#!/usr/bin/env python3
"""Check frozen source bytes and final explicit Lean probe results."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def probes(source: str, log: str, count: int) -> None:
    code = (HERE / source).read_text()
    output = (HERE / log).read_text()
    names = re.findall(r"^#check @([^\s]+)$", code, re.M)
    axioms = re.findall(r"^#print axioms ([^\s]+)$", code, re.M)
    assert len(names) == len(set(names)) == count
    assert names == axioms
    assert not re.search(r"\b(error|warning|sorryAx)\b|\[truncated\]", output)
    blocks = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output, re.S)
    assert len(blocks) == count, (log, len(blocks), count)
    assert {name for name, _ in blocks} == set(names)
    for name, dependencies in blocks:
        used = {item.strip().split('.{')[0] for item in dependencies.split(',') if item.strip()}
        assert used <= ALLOWED, (name, used)
        assert re.search(re.escape(name) + r"(?:\.\{[^}]*\})?\s*:", output), name
    for option in ["pp.explicit", "pp.fullNames", "pp.proofs", "pp.universes", "pp.deepTerms"]:
        assert f"set_option {option} true" in code
    steps = re.search(r"set_option pp.maxSteps (\d+)", code)
    assert steps and int(steps.group(1)) >= 1000000
    print(f"PASS {count} explicit axiom/signature pairs: {log}")


def main() -> None:
    for name in ["comparison-mass-direct-3.log", "selection-mass-direct-3.log"]:
        assert (HERE / name).stat().st_size == 0, name
    print("PASS both absolute-path strict production logs are empty")
    for name, jobs in [("comparison-mass-canonical-1.log", 1212), ("selection-mass-canonical-1.log", 1213)]:
        output = (HERE / name).read_text()
        assert f"Build completed successfully ({jobs} jobs)." in output
        assert "error:" not in output
        print(f"PASS delegated canonical target: {name} ({jobs} jobs)")
    probes("selection-mass-public.lean", "selection-mass-public-1.log", 22)
    probes("selection-mass-kernels.lean", "selection-mass-kernels-2.log", 2)
    expected = {
        "lean/MicroCFTA/SourceMergedComparisonMass.lean": "ad09e92efeb8507f3262c48947348e031491273be648f8855c6d01ad9d2891d0",
        "lean/MicroCFTA/SourceMergedSelectionMass.lean": "5f99d4c647468393489d7957d6ca3a6617f64094107a431b37f488f0a013d3e4",
        "lean/MicroCFTA/SourceCurrentAllocatedProjectionResources.lean": "ee3d7393150a44ab035ef8edb446816128ef8e3dd33528047c222eceff37c42e",
    }
    for path, sha in expected.items():
        assert digest(ROOT / path) == sha, path
    print("PASS final production sources and reader dependency match frozen hashes")
    if "--checks-only" not in sys.argv:
        manifest = json.loads((HERE / "selection-mass-manifest.json").read_text())
        assert manifest["file_count"] == len(manifest["files"])
        for item in manifest["files"]:
            path = ROOT / item["path"]
            assert path.stat().st_size == item["bytes"], item["path"]
            assert digest(path) == item["sha256"], item["path"]
        print(f"PASS {manifest['file_count']} frozen hashes and byte counts")


if __name__ == "__main__":
    main()
