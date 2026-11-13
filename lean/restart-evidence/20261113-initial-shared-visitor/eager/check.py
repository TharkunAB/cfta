from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def record(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text())


def apply_patch(source: bytes, delta: Path) -> bytes:
    with tempfile.TemporaryDirectory(prefix="initial-eager-source-") as scratch:
        path = Path(scratch) / "source.lean"
        path.write_bytes(source)
        result = subprocess.run(
            ["patch", "--silent", "--batch", "--fuzz=0", str(path)],
            input=delta.read_bytes(), capture_output=True, check=False)
        assert result.returncode == 0, (delta, result.stdout, result.stderr)
        return path.read_bytes()


def main() -> None:
    parser = argparse.ArgumentParser(description="Reconstruct and hash source only. No compiler or network action.")
    parser.add_argument("--extract", type=Path)
    parser.add_argument("--sourcepins", type=Path, help="Optional repository root for original source pin checks.")
    arguments = parser.parse_args()
    history = record(ROOT / "source-history.json")
    inventory = record(ROOT / "inventory.json")
    for item in inventory["files"]:
        data = (ROOT / item["file"]).read_bytes()
        assert sha(data) == item["sha256"], item["file"]
        assert len(data) == item["bytes"], item["file"]
    family, = history["families"]
    base = family["base"]
    current = (ROOT / base["file"]).read_bytes()
    assert sha(current) == base["sha256"]
    sources = {base["name"]: current}
    parent = base["name"]
    for item in family["stages"]:
        assert item["parent"] == parent
        current = apply_patch(current, ROOT / item["patch"])
        assert sha(current) == item["sha256"], item["name"]
        assert len(current) == item["bytes"]
        assert len(current.splitlines()) == item["lines"]
        sources[item["name"]] = current
        parent = item["name"]
    assert len(sources) == history["expected_source_stages"]
    assert len(family["stages"]) == history["expected_zero_context_transitions"]
    actual_inputs: dict[str, bytes] = {}
    for item in history["checks"]:
        actual = apply_patch(sources[item["stage"]], ROOT / item["instrumentation"]["file"])
        assert sha(actual) == item["instrumented_sha256"], item["name"]
        report = record(ROOT / item["report"]["file"])
        assert report["sha256"] == sha(actual)
        assert report["compiler_exit"] == item["compiler_exit"]
        assert report["limits"] == item["limits"]
        if item["name"] != "check6":
            assert not item["proof_credit"] and report["compiler_exit"] == 1
        else:
            assert report["compiler_exit"] == 0 and item["proof_credit"]
            assert len(item["axiom_reports"]) == 2
            for declaration in item["axiom_reports"]:
                assert set(declaration["axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
        actual_inputs[item["name"]] = actual
    assert len(actual_inputs) == history["expected_instrumentation_replays"]
    ancillary: dict[str, bytes] = {}
    for item in history["ancillary_assembly_snapshots"]:
        data = apply_patch(sources[item["parent"]], ROOT / item["patch"])
        assert sha(data) == item["sha256"], item["name"]
        ancillary[item["name"]] = data
    assert len(ancillary) == history["expected_ancillary_transitions"]
    by_sha = {item["sha256"]: ROOT / item["file"] for item in history["attachments"]}
    headers = history["approved_headers"]
    canonical = by_sha[headers["canonical_sha256"]].read_bytes()
    global_header = by_sha[headers["global_sha256"]].read_bytes()
    extra = by_sha[headers["global_extra_sha256"]].read_text()
    original = by_sha[headers["original_header_sha256"]].read_text()
    assert global_header.decode().replace(extra, "", 1).replace(
        "private theorem accepted_initial_prefix\n", "theorem accepted\n", 1) == original
    for name, source in sources.items():
        assert canonical in source
        if name != "control-115":
            assert global_header in source
    if arguments.sourcepins is not None:
        candidates = [item for item in history["attachments"]
                      if item["original_source"].endswith("source-pins.json")]
        for item in candidates:
            for path, expected in record(ROOT / item["file"]).items():
                assert sha((arguments.sourcepins / path).read_bytes()) == expected, path
    if arguments.extract is not None:
        arguments.extract.mkdir(parents=True, exist_ok=False)
        for name, data in sources.items():
            (arguments.extract / (name + ".lean")).write_bytes(data)
        for name, data in actual_inputs.items():
            (arguments.extract / (name + "-instrumented.lean")).write_bytes(data)
        for name, data in ancillary.items():
            (arguments.extract / (name + ".lean.txt")).write_bytes(data)
    print(json.dumps({"source_stages": len(sources), "source_transitions": len(sources) - 1,
                      "instrumentation_transitions": len(actual_inputs),
                      "ancillary_transitions": len(ancillary), "compiler_run": False,
                      "check6_original_report": "PASS_STRICT_STANDARD_AXIOMS"}, indent=2))


if __name__ == "__main__":
    main()
