from __future__ import annotations

import datetime
import hashlib
import json
import re
import subprocess
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent
PACKET = ROOT / "packet"
HISTORY = PACKET / "history"
OBJECTS = PACKET / "objects"
for directory in (PACKET, HISTORY, OBJECTS):
    directory.mkdir(exist_ok=True)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def describe(path: Path) -> dict[str, Any]:
    data = path.read_bytes()
    return {"file": str(path.relative_to(PACKET)), "sha256": digest(data),
            "bytes": len(data), "lines": len(data.splitlines())}


object_paths: dict[str, Path] = {}


def attach(path: Path, label: str) -> dict[str, Any]:
    data = path.read_bytes()
    key = digest(data)
    if key not in object_paths:
        suffix = path.suffix or ".txt"
        target = OBJECTS / (key + suffix)
        target.write_bytes(data)
        object_paths[key] = target
    return describe(object_paths[key]) | {"original_source": str(path), "label": label}


def patch(before: Path, after: Path, name: str) -> dict[str, Any]:
    target = HISTORY / name
    result = subprocess.run(
        ["diff", "-U0", "--label", before.name, "--label", after.name,
         str(before), str(after)], capture_output=True, check=False)
    assert result.returncode == 1, (before, after, result.returncode, result.stderr)
    assert result.stdout.startswith(b"--- ")
    target.write_bytes(result.stdout)
    return describe(target)


body = Path("/tmp/mcfta-current-initial-eager-invocation-body-20261113-1808")
stage_sources = [
    ("control-115", body / "SourceSynthesisCurrentInitialEagerControl.lean"),
    ("combined-285", body / "SourceSynthesisCurrentInitialEagerInvocation.lean"),
    ("qname-285", Path("/tmp/mcfta-current-initial-eager-invocation-repair1-20261113-1814/SourceSynthesisCurrentInitialEagerInvocation.lean")),
    ("branch-284", Path("/tmp/mcfta-current-initial-eager-invocation-repair2-20261113-1818/SourceSynthesisCurrentInitialEagerInvocation.lean")),
    ("depth-289", Path("/tmp/mcfta-current-initial-eager-invocation-repair3-20261113-1822/SourceSynthesisCurrentInitialEagerInvocation.lean")),
    ("fuel-290", Path("/tmp/mcfta-current-initial-eager-invocation-repair4-20261113-1827/SourceSynthesisCurrentInitialEagerInvocation.lean")),
    ("receipts-306", Path("/tmp/mcfta-current-initial-eager-invocation-repair5-20261113-1833/SourceSynthesisCurrentInitialEagerInvocation.lean")),
]
stage_by_name = dict(stage_sources)
base_path = HISTORY / "base-control-115.lean.txt"
base_path.write_bytes(stage_sources[0][1].read_bytes())
base = describe(base_path) | {
    "name": "control-115", "original_source": str(stage_sources[0][1]),
    "status": "EXACT_CONTROL_PREFIX_CHECKED_IN_FINAL_COMBINED_SOURCE_NO_STANDALONE_RUN"}
stages: list[dict[str, Any]] = []
for index, ((previous_name, previous), (name, source)) in enumerate(
        zip(stage_sources, stage_sources[1:]), 1):
    delta = patch(previous, source, f"{index:02d}-{name}.patch")
    stages.append({"name": name, "parent": previous_name,
                   "patch": delta["file"], "patch_sha256": delta["sha256"],
                   "sha256": digest(source.read_bytes()), "bytes": source.stat().st_size,
                   "lines": len(source.read_bytes().splitlines()), "original_source": str(source),
                   "status": "PASS_STRICT_STANDARD_AXIOMS" if index == 6
                   else "FAILED_STRICT_NO_PROOF_CREDIT"})

checks: list[dict[str, Any]] = []
check_roots = [
    "/tmp/mcfta-initial-eager-invocation-check1-20261113-1813",
    "/tmp/mcfta-initial-eager-invocation-check2-20261113-1815",
    "/tmp/mcfta-initial-eager-invocation-check3-20261113-1819",
    "/tmp/mcfta-initial-eager-invocation-check4-20261113-1824",
    "/tmp/mcfta-initial-eager-invocation-check5-20261113-1828",
    "/tmp/mcfta-initial-eager-invocation-check6-20261113-1834",
]
for index, check_root in enumerate(check_roots, 1):
    directory = Path(check_root)
    stage_name, stage_source = stage_sources[index]
    actual = directory / "check.lean"
    report_path = directory / "draft-checked.json"
    report = json.loads(report_path.read_text())
    assert report["sha256"] == digest(actual.read_bytes())
    assert report["compiler_exit"] == (0 if index == 6 else 1)
    assert report["limits"] == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
    output = (directory / "draft-output.txt").read_text()
    axioms = [{"name": name, "axioms": [item.strip() for item in items.split(",") if item.strip()]}
              for name, items in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output, re.S)]
    if index == 6:
        assert len(axioms) == 2
        assert all(set(item["axioms"]) == {"propext", "Classical.choice", "Quot.sound"} for item in axioms)
    instrument = patch(stage_source, actual, f"instrument-check{index}.patch")
    entry = {
        "name": f"check{index}", "stage": stage_name,
        "instrumented_sha256": digest(actual.read_bytes()),
        "instrumented_lines": len(actual.read_bytes().splitlines()),
        "instrumentation": instrument,
        "compiler_exit": report["compiler_exit"],
        "status": "PASS_STRICT_STANDARD_AXIOMS" if index == 6 else "FAILED_STRICT_NO_PROOF_CREDIT",
        "proof_credit": index == 6,
        "diagnostics": attach(directory / "draft-output.txt", f"check{index} exact output"),
        "report": attach(report_path, f"check{index} exact strict report"),
        "checker": attach(directory / "check-draft.py", f"check{index} original strict checker"),
        "instrumented_hash_record": attach(directory / "instrumented.sha256", f"check{index} original input hash"),
        "actual_input_original_path": str(actual),
        "axiom_reports": axioms,
        "limits": report["limits"],
        "scoped_print_all": index == 5,
    }
    peaks = directory / "peaks"
    entry["peaks"] = attach(peaks, f"check{index} exact peaks") if peaks.exists() else None
    if not peaks.exists():
        entry["peaks_status"] = "NOT_PRESENT_IN_ORIGINAL_CHECK_DIRECTORY_NO_VALUE_INVENTED"
    checks.append(entry)

attachments: list[dict[str, Any]] = []
plan_roots = [
    Path("/tmp/mcfta-current-initial-eager-invocation-plan-20261113-1757"),
    Path("/tmp/mcfta-current-initial-eager-invocation-plan-final-20261113-1800"),
]
for directory in plan_roots:
    for source in sorted(directory.iterdir()):
        if source.is_file():
            attachments.append(attach(source, f"APPROVED_PLAN_ONLY:{directory.name}:{source.name}"))
for directory in [body, *[path.parent for _, path in stage_sources[2:]]]:
    for source in sorted(directory.iterdir()):
        if source.is_file() and source.suffix != ".lean" and not source.name.endswith(".header-join-first.txt"):
            attachments.append(attach(source, f"SOURCE_STAGE_METADATA:{directory.name}:{source.name}"))

ancillary: list[dict[str, Any]] = []
for name, parent_name, source in [
    ("uncompiled-first-control-join", "control-115", body / "SourceSynthesisCurrentInitialEagerControl.lean.header-join-first.txt"),
    ("uncompiled-first-global-join", "combined-285", body / "SourceSynthesisCurrentInitialEagerInvocation.lean.header-join-first.txt"),
]:
    delta = patch(stage_by_name[parent_name], source, f"ancillary-{name}.patch")
    ancillary.append({"name": name, "parent": parent_name, "patch": delta["file"],
                      "patch_sha256": delta["sha256"], "sha256": digest(source.read_bytes()),
                      "bytes": source.stat().st_size, "lines": len(source.read_bytes().splitlines()),
                      "original_source": str(source), "status": "UNCHECKED_ASSEMBLY_SNAPSHOT_NO_PROOF_CREDIT"})

approved = plan_roots[1]
canonical = (approved / "canonical-header.lean.txt").read_bytes()
global_header = (approved / "global-header.lean.txt").read_bytes()
extra = (approved / "global-extra.lean.txt").read_text()
original_header = (approved / "original-header.lean.txt").read_text()
assert global_header.decode().replace(extra, "", 1).replace("private theorem accepted_initial_prefix\n", "theorem accepted\n", 1) == original_header
for name, source in stage_sources:
    assert canonical in source.read_bytes()
    if name != "control-115":
        assert global_header in source.read_bytes()
control_prefix = base_path.read_bytes().split(b"\nend MicroCFTA.SourceSynthesisCurrentProgramEagerOutputs\n")[0]
assert all(source.read_bytes().startswith(control_prefix) for _, source in stage_sources[1:])

tool = subprocess.run(["diff", "--version"], capture_output=True, text=True, check=True).stdout.splitlines()[0]
manifest = {
    "schema": "initial-eager-invocation-source-history-v1",
    "prepared_at": datetime.datetime.now().astimezone().isoformat(),
    "status": "PRIVATE_CONTROL_AND_INITIAL_PREPARATION_BRIDGE_CHECKED_PUBLIC_AND_AUDIT_PENDING",
    "scope": "Only the canonical initial eager invocation and same-initializer prefix/preparation source family. No visitor source family or later row/partial-model soundness.",
    "families": [{"name": "initial-eager-invocation", "base": base, "stages": stages}],
    "checks": checks,
    "attachments": attachments,
    "ancillary_assembly_snapshots": ancillary,
    "approved_headers": {"canonical_sha256": digest(canonical), "global_sha256": digest(global_header),
                         "global_extra_sha256": digest(extra.encode()), "original_header_sha256": digest(original_header.encode()),
                         "all_stage_headers_exact": True, "old_header_inverse_exact": True},
    "diff_tool": tool,
    "expected_source_stages": 7,
    "expected_zero_context_transitions": 6,
    "expected_instrumentation_replays": 6,
    "expected_ancillary_transitions": 2,
    "replay_execution": "NOT_RUN_BY_PREPARER",
    "standalone_control_compile": "NOT_RUN; exact prefix of combined check6 supplies the checked declaration",
    "public_laws_added": 0,
    "haskell_changes": False,
    "haskell_fixes": [],
    "source_proof_scope": "One same current accepted initializer and stable eager outcome retain the entire prior receipt. Every initial expansion selects slot zero. Positive initial expansion uses the canonical actual prefix, and actual supported preparation rows retain original-root row origin. No emitted Type assignment or ordinary typing conclusion is proved here.",
}
(PACKET / "source-history.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps({"packet": str(PACKET), "source_stages": 7, "source_transitions": 6,
                  "instrumentation_transitions": 6, "ancillary_transitions": 2,
                  "objects": len(object_paths), "check6": checks[-1]["status"]}, indent=2))
