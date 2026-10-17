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
    assert (HERE / "row-uniform-direct-2.log").stat().st_size == 0
    print("PASS absolute-path strict production log is empty")
    canonical = (HERE / "row-uniform-canonical-1.log").read_text()
    assert "Build completed successfully (1218 jobs)." in canonical
    assert "error:" not in canonical
    print("PASS delegated canonical target: 1218 jobs")
    probes("row-uniform-public.lean", "row-uniform-public-1.log", 5)
    probes("row-uniform-kernels.lean", "row-uniform-kernels-2.log", 2)
    expected = {'lean/MicroCFTA/SourceCurrentAllocatedRowReadUniform.lean': '535eeabd77b6e9582a564f7b41d9456c5b99c77c7a0a73f300a0871dc4e9155d', 'lean/MicroCFTA/SourceCurrentAllocatedRowReadNumeric.lean': 'eb9f8391cdc7630f6c113ea160002711d570eee5b46786cdb6396490fd40a4fc', 'lean/MicroCFTA/SourceCurrentAllocatedReaderNumeric.lean': '47b4a8c3564818237557ac54515a367702fa2a8f3141b08a6eb6d2237a7e32a7', 'lean/MicroCFTA/SourceCurrentAllocatedReaderControl.lean': '11b325bf91fd152ac65c6c3d7dab35ffbd5cb4d44e54551dc1cc750795e15d39', 'lean/MicroCFTA/HeightOrderControlled.lean': 'a98abdc7880f17c9de7b6f3aa78a963aa9a7e6f3c22e52858d46af0b345f86a4', 'lean/MicroCFTA/SourceEqualityProjectionRead.lean': 'f299b66171bdf9452fa2b62b22ddca3371a1fb4916193a57d1fd5ece59f8551d', 'lean/MicroCFTA/MergedComparisonCompletion.lean': '50b3b3a285d8fe00ae08ecd7f513a51aada597ae59b939c794a84c57fc951baa', 'lean/MicroCFTA/MergedFreshOrdinaryColdReplay.lean': '534edc0c053b025623921f63c9d3fa0e874854561392055439925c3244eaba6f', 'lean/MicroCFTA/SourceEqualityRequiredSemanticCache.lean': '797e08006478d3a1236fe3aafd33e9983ae4f211bf29d298afdc236b3dd96420', 'lean/MicroCFTA/InternedFreshOrdinaryClosedCompletion.lean': '95f716f12c12353ea549d5fec40725224ed0ff8ba31dbf174c95e79288e376bc'}
    for path, known in expected.items():
        assert digest(ROOT / path) == known, path
    print("PASS final source and immutable dependency hashes")
    if "--checks-only" not in sys.argv:
        manifest = json.loads((HERE / "row-uniform-manifest.json").read_text())
        assert manifest["file_count"] == len(manifest["files"])
        for entry in manifest["files"]:
            path = ROOT / entry["path"]
            assert path.stat().st_size == entry["bytes"], entry["path"]
            assert digest(path) == entry["sha256"], entry["path"]
        print(f"PASS {manifest['file_count']} frozen hashes and byte counts")

if __name__ == "__main__":
    main()
