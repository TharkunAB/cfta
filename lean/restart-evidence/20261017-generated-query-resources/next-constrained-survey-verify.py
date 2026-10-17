#!/usr/bin/env python3
"""Check the frozen survey inputs and reproduce the exact header excerpts."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
PREFIX = "lean/MicroCFTA/"
SPECS = [
    ("SourceCurrentConstrainedCapGeneratedQueryResources.lean", ["Fits", "Frame", "Receipt", "complete"]),
    ("SourceCurrentConstrainedCapGeneratedQuerySequence.lean", ["Supported", "Pool", "Run", "complete_many"]),
    ("SourceCurrentAllocatedNativeResourceForecast.lean", ["Profile", "step", "Room", "Reserved"]),
    ("SourceCurrentConstrainedCapCurrentNative.lean", ["At", "advance", "step"]),
    ("SourceCurrentConstrainedCapMixedTarget.lean", ["operandDepth", "foldDepth", "targetDepth", "operand_complete", "fold", "target_reads"]),
    ("SourceCurrentConstrainedCapMixedShared.lean", ["Certificate", "Stored", "force_receipt", "leaf_receipt"]),
    ("SourceCurrentConstrainedCapMixedEdit.lean", ["outputDepth", "node", "children", "rows", "list"]),
    ("SourceCurrentConstrainedCapMixedClass.lean", ["classDepth", "verified"]),
    ("SourceCurrentConstrainedCapMixedClassPass.lean", ["foldDepth", "fold", "pass"]),
    ("SourceCurrentAllocatedTargetGraph.lean", ["Operand", "Fold", "Target", "FoldRanges", "TargetRanges"]),
    ("SourceCurrentAllocatedTargetComplete.lean", ["Receipt", "FoldReads", "TargetReads", "fold_complete", "target_complete"]),
    ("SourceCurrentAllocatedSharedTargetForce.lean", ["Force", "Reads", "ForceRanges", "Receipt", "complete"]),
    ("SourceCurrentMemoMergeGraph.lean", ["Entry", "Code", "retainedColumn", "small", "column", "large", "group", "body", "Run", "Call"]),
    ("SourceCurrentConstrainedCapSelectedProjection.lean", ["forest", "forest_complete"]),
    ("SourceCurrentAllocatedPartialGraph.lean", ["NodeCall", "NodeBody", "EdgeCall", "EdgeBody", "Rows", "Descendants", "Children", "Walk"]),
    ("SourceCurrentAllocatedPartialActiveOrder.lean", ["nodeRank", "edgeRank", "ActiveExcept", "ReturnedBounds", "returned_child_lt"]),
    ("SourceCurrentAllocatedFiniteOrdinaryOuterResourceDefs.lean", ["Headroom", "Below"]),
    ("SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned.lean", ["NodeCertificate", "EdgeCertificate", "Stored", "Stored.finishEdge"]),
    ("SourceCurrentAllocatedNativeInventoryRebase.lean", ["extend", "rebase"]),
]
HASKELL = "cfta/src/Data/CFTA/Equality/Operations.hs"
HASKELL_RANGES = [(75, 145), (171, 234), (235, 336)]
SOURCES = [PREFIX + name for name, _ in SPECS] + [HASKELL]
DECL = re.compile(r"^[ \t]*(?:noncomputable\s+)?(def|theorem|structure|inductive|abbrev)\s+(\S+)")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def excerpts() -> str:
    chunks = ["Exact selected source headers and graph constructors.\nTheorems stop before their proof. Source hashes are recorded in the survey manifest.\n"]
    for name, names in SPECS:
        rel = PREFIX + name
        lines = (ROOT / rel).read_text().splitlines()
        for wanted in names:
            matches = [(i, m) for i, line in enumerate(lines) if (m := DECL.match(line)) and m.group(2) == wanted]
            if len(matches) != 1:
                raise AssertionError((rel, wanted, len(matches)))
            start, match = matches[0]
            kind = match.group(1)
            end = start
            selected = []
            for i in range(start, len(lines)):
                line = lines[i]
                if i > start and (DECL.match(line) or line.startswith("/--") or line.startswith("end")):
                    break
                if kind == "theorem" and ":=" in line:
                    selected.append(line.split(":=", 1)[0].rstrip())
                    end = i
                    break
                selected.append(line)
                end = i
                if kind not in ("structure", "inductive") and ":=" in line:
                    # Definitions retain their literal body until the next declaration/comment.
                    continue
            while selected and not selected[-1]:
                selected.pop()
                end -= 1
            chunks.append(f"\n{rel}:{start + 1}-{end + 1}\n" + "\n".join(selected) + "\n")
    lines = (ROOT / HASKELL).read_text().splitlines()
    for start, end in HASKELL_RANGES:
        chunks.append(f"\n{HASKELL}:{start}-{end}\n" + "\n".join(lines[start - 1:end]) + "\n")
    return "".join(chunks)


def main() -> None:
    assert len(SOURCES) == len(set(SOURCES)) == 20
    exact = excerpts()
    output = HERE / "next-constrained-survey-headers.txt"
    if "--write-headers" in sys.argv:
        output.write_text(exact)
        print("WROTE exact excerpts for 20 production files")
        return
    assert output.read_text() == exact, "source excerpts changed"
    assert digest(ROOT / SOURCES[0]) == "ea07e400b4a56ab3b22795119f978a1e7a0de25b39e78a2455a2c0baaf23db4f"
    assert digest(ROOT / SOURCES[1]) == "15210f2a3370710f9e5e07ee09999ec271b036ccfe2fba017d1187f017c86d5f"
    if "--inputs-only" not in sys.argv:
        manifest = json.loads((HERE / "next-constrained-survey-manifest.json").read_text())
        assert manifest["source_files"] == 20
        assert manifest["file_count"] == len(manifest["files"])
        for item in manifest["files"]:
            path = ROOT / item["path"]
            assert path.stat().st_size == item["bytes"], item["path"]
            assert digest(path) == item["sha256"], item["path"]
        print(f"PASS {manifest['file_count']} frozen hashes and byte counts")
    print("PASS exact headers/constructors and Haskell excerpts from 20 production files")
    print("PASS current generated-query sources match the root's final frozen hashes")
    print("Read-only evidence check; no new Lean theorem or Haskell execution was asserted")


if __name__ == "__main__":
    main()
