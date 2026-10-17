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
    assert (HERE / "reader-control-direct-4.log").stat().st_size == 0
    print("PASS absolute-path strict production log is empty")
    canonical = (HERE / "reader-control-canonical-1.log").read_text()
    assert "Build completed successfully (1212 jobs)." in canonical
    assert "error:" not in canonical
    print("PASS delegated canonical target: 1212 jobs")
    probes("reader-control-public.lean", "reader-control-public-1.log", 23)
    probes("reader-control-kernels.lean", "reader-control-kernels-4.log", 2)
    expected = {'lean/MicroCFTA/SourceCurrentAllocatedReaderControl.lean': '11b325bf91fd152ac65c6c3d7dab35ffbd5cb4d44e54551dc1cc750795e15d39', 'lean/MicroCFTA/SourceCurrentAllocatedProjectionResources.lean': 'ee3d7393150a44ab035ef8edb446816128ef8e3dd33528047c222eceff37c42e', 'lean/MicroCFTA/MergedFreshOrdinaryColdTermination.lean': 'ab9083a8a5b8046651c920382118828ac1ca80ff1ca5cc55481a8ffe17362b47', 'lean/MicroCFTA/InternedMuDepthInventory.lean': 'dde5c556d862bb90158bcd2cfc813c36cedaad6b67e0d4e611f85e6f6a1a1693', 'lean/MicroCFTA/MergedColdReaderTermination.lean': '78c63c9a8a87d6671cf59e27f88756bdafbc3652e0493b8868a09f206ed843d8', 'lean/MicroCFTA/SourceCurrentAllocatedRecursiveMassTrace.lean': 'e9578e2d8fa8aea3eea4eab1dbf03eb8ba5476448976ff4fef1964518fda11b8', 'lean/MicroCFTA/SourceCurrentAllocatedRecursiveMassMonotone.lean': '707fa9615c64ef7cf024d9af0a680e12647fa2b5a7cec5da1ec1581beb1fe57c', 'lean/MicroCFTA/InternedValueMassHeap.lean': '7505bb38a993efb0bdb48cd772a2ace9a9054c33f1e1050acbf1bc8a51242c19', 'lean/MicroCFTA/InternedValueMass.lean': 'ea2d4e567fdede7d481d5c1819813c8e5f64aa68d8773d6fdb0599f3b5f5c628', 'lean/MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean': '95f716f12c12353ea549d5fec40725224ed0ff8ba31dbf174c95e79288e376bc'}
    for path, sha in expected.items():
        assert digest(ROOT / path) == sha, path
    print("PASS final production source and immutable read dependencies")
    if "--checks-only" not in sys.argv:
        manifest = json.loads((HERE / "reader-control-manifest.json").read_text())
        assert manifest["file_count"] == len(manifest["files"])
        for item in manifest["files"]:
            path = ROOT / item["path"]
            assert path.stat().st_size == item["bytes"], item["path"]
            assert digest(path) == item["sha256"], item["path"]
        print(f"PASS {manifest['file_count']} frozen hashes and byte counts")


if __name__ == "__main__":
    main()
