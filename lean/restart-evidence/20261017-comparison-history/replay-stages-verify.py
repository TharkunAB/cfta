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
    assert (HERE / "replay-stages-direct-2.log").stat().st_size == 0
    print("PASS absolute-path strict production log is empty")
    canonical = (HERE / "replay-stages-canonical-1.log").read_text()
    assert "Build completed successfully (1220 jobs)." in canonical
    assert "error:" not in canonical
    print("PASS delegated canonical target: 1220 jobs")
    probes("replay-stages-public.lean", "replay-stages-public-1.log", 4)
    probes("replay-stages-kernels.lean", "replay-stages-kernels-4.log", 2)
    expected = {'lean/MicroCFTA/SourceMergedComparisonReplayStages.lean': 'fb2153f3a37bb39d8b931bd16d3e40f1d390dd4e286d983366daa49d03f697c0', 'lean/MicroCFTA/SourceMergedComparisonHistory.lean': '0d186e5bb9ab969997f57a281d3958d3bf4f2a8f961e0ddade81c413245652c2', 'lean/MicroCFTA/SourceCurrentAllocatedUnfoldHistory.lean': '226eef7e648d3e26ed58829ab445def36c689f218b3e4961b6b9d0440dea084f', 'lean/MicroCFTA/SourceCurrentAllocatedReaderHistory.lean': 'e7c92463f91abb1f2024aa63429944b298d42e2af8d56a96fa455e289656f728', 'lean/MicroCFTA/SourceMergedComparisonBudget.lean': '637db47284b4979535a9ad69ac21c18a9ccae1d07cba09afea0063e98bc2bd90', 'lean/MicroCFTA/SourceMergedComparisonEffects.lean': '997a08de2d62004ab4534bed36b5ca08532a36530b515cef5afe57289a3d9c18', 'lean/MicroCFTA/MergedSourceComparison.lean': '215330f70fa1b4ad03924607a653c5ebce213f866f2cc1f588a3b25ce25132fc', 'lean/MicroCFTA/MergedFreshOrdinaryComparison.lean': '595918dd693ba7f83f0d91f148086ba19bdab0b4977ddd3ead040816353560dc', 'lean/MicroCFTA/SourceEqualityProjectionRead.lean': 'f299b66171bdf9452fa2b62b22ddca3371a1fb4916193a57d1fd5ece59f8551d', 'lean/MicroCFTA/SourceMergedComparisonStability.lean': '94a1896238f7a962718ecbb2e0a82274de5e216d1c624af0f1f9f4f9af4d11ee', 'lean/MicroCFTA/SourceEqualityRequiredSemanticCache.lean': '797e08006478d3a1236fe3aafd33e9983ae4f211bf29d298afdc236b3dd96420', 'lean/MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean': '95f716f12c12353ea549d5fec40725224ed0ff8ba31dbf174c95e79288e376bc'}
    for path, known in expected.items():
        assert digest(ROOT / path) == known, path
    print("PASS final source and immutable dependency hashes")
    if "--checks-only" not in sys.argv:
        manifest = json.loads((HERE / "replay-stages-manifest.json").read_text())
        assert manifest["file_count"] == len(manifest["files"])
        for entry in manifest["files"]:
            path = ROOT / entry["path"]
            assert path.stat().st_size == entry["bytes"], entry["path"]
            assert digest(path) == entry["sha256"], entry["path"]
        print(f"PASS {manifest['file_count']} frozen hashes and byte counts")

if __name__ == "__main__":
    main()
