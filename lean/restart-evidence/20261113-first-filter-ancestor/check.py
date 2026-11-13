#!/usr/bin/env python3
"""Reconstruct the recorded source stages without invoking Lean."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def apply_patch(root: Path, patch: Path) -> None:
    result = subprocess.run(
        ["patch", "--batch", "--forward", "--fuzz=0", "-p0", "-i", str(patch)],
        cwd=root, capture_output=True, text=True)
    assert result.returncode == 0, (str(patch), result.stdout, result.stderr)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path)
    parser.add_argument("--extract", type=Path)
    args = parser.parse_args()
    packet = Path(__file__).resolve().parent
    expected = json.loads((packet / "SHA256.json").read_text())
    assert set(expected) == {str(p.relative_to(packet)) for p in packet.rglob("*")
        if p.is_file() and p.name != "SHA256.json"}
    for name, value in expected.items():
        assert digest((packet / name).read_bytes()) == value, name
    manifest = json.loads((packet / "manifest.json").read_text())
    old_header = (packet / "headers/00-approved-unparsed-header.lean.txt").read_text()
    new_header = (packet / "headers/01-typed-header.lean.txt").read_text()
    assert len(old_header.splitlines()) == len(new_header.splitlines()) == 72
    expanded = old_header.replace(
        "∃ typesExpression functionExpression argumentExpression\n",
        "∃ (typesExpression functionExpression argumentExpression : SourceSynthesisFirstOrderConstruction.Expression)\n").replace(
        "          nodeStart nodeMiddle nodeAfter (rawRows : List (EdgeValue Symbol Guard))",
        "          (nodeStart nodeMiddle nodeAfter : State Symbol Guard) (rawRows : List (EdgeValue Symbol Guard))")
    assert expanded == new_header
    final_raw = final_instrumented = b""
    with tempfile.TemporaryDirectory(prefix="first-filter-source-check-") as directory:
        work = Path(directory)
        source = work / "source.lean"
        source.write_bytes((packet / "source/00-initial.lean.txt").read_bytes())
        for stage in manifest["stages"]:
            if stage["source_patch"]:
                apply_patch(work, packet / stage["source_patch"])
            raw = source.read_bytes()
            assert digest(raw) == stage["raw_sha256"]
            assert len(raw.decode().splitlines()) == stage["raw_lines"]
            assert not re.search(r"\b(?:sorry|admit|axiom)\b", raw.decode())
            begin = raw.decode().index("private theorem first_filter_current_app_source_ancestor")
            header = raw.decode()[begin:raw.decode().index(" := by\n", begin)] + "\n"
            assert header == (old_header if stage["stage"] == 1 else new_header)
            apply_patch(work, packet / stage["instrumentation_patch"])
            instrumented = source.read_bytes()
            assert digest(instrumented) == stage["instrumented_sha256"]
            text = raw.decode()
            marker = "end MicroCFTA.SourceSynthesisFirstFilterCurrentAppSourceAncestor\n"
            assert instrumented.decode() == text.replace(marker,
                "#print axioms first_filter_current_app_source_ancestor\n\n" + marker)
            report = json.loads((packet / stage["report"]).read_text())
            assert report["sha256"] == digest(instrumented)
            assert report["compiler_exit"] == (0 if stage["stage"] == 6 else 1)
            assert report["public_laws_added"] == 0
            assert report["limits"] == {"memory.max": "4294967296",
                "memory.high": "4294967296", "memory.swap.max": "0"}
            final_raw, final_instrumented = raw, instrumented
            source.write_bytes(raw)
        source.write_text(old_header)
        apply_patch(work, packet / "headers/header-types-only.patch")
        assert source.read_text() == new_header
    assert digest(final_raw) == manifest["expected_final_raw_sha256"]
    final_output = (packet / manifest["stages"][-1]["output"]).read_text()
    assert "sorryAx" not in final_output and "error:" not in final_output
    assert "depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in final_output
    if args.repo:
        for dependency in manifest["direct_imports"]:
            assert digest((args.repo / dependency["path"]).read_bytes()) == dependency["sha256"], dependency["path"]
    if args.extract:
        args.extract.mkdir(parents=True, exist_ok=True)
        for name, data in [("SourceSynthesisFirstFilterCurrentAppSourceAncestor.lean", final_raw),
                ("SourceSynthesisFirstFilterCurrentAppSourceAncestor-instrumented.lean", final_instrumented)]:
            target = args.extract / name
            assert not target.exists(), str(target)
            target.write_bytes(data)
    print(json.dumps({"status": "PASS", "source_stages": 6, "historical_compiler_checks": 6,
        "strict_final_compiler_exit": 0, "public_laws_added": 0,
        "final_raw_sha256": digest(final_raw), "final_instrumented_sha256": digest(final_instrumented),
        "lean_rerun": False}, sort_keys=True))


if __name__ == "__main__":
    main()
