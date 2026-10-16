"""Verify the drawn-field refresh and literal local reduction checkpoint."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--require-current", action="store_true")
args = parser.parse_args()


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*arguments: str) -> str:
    return subprocess.run(["git", *arguments], cwd=root, check=True, text=True, capture_output=True).stdout


def other_worktrees(text: str) -> list[str]:
    return [block for block in text.strip().split("\n\n") if not block.startswith(f"worktree {root}\n")]


baseline_file = evidence / "starting-sha256.json"
baseline = json.loads(baseline_file.read_text())
missing = sorted(name for name in baseline if not (root / name).is_file())
changed = sorted(name for name, expected in baseline.items() if (root / name).is_file() and digest(root / name) != expected)
authorities = {
    "NEXT-PROMPT.md", "HANDOFF.md", "FINDINGS.md", "lean/README.md",
    "lean/SYSTEM.md", "lean/API-COVERAGE.md", "lean/COVERAGE.md",
}
upstream = git("diff", "--name-only", "5399d310", "c0cc8a05").splitlines()
proofs = [name for name in baseline if name.startswith("lean/MicroCFTA/") and name.endswith(".lean") and name != "lean/MicroCFTA/Audit.lean"]
allowed = authorities | set(upstream) | {"lean/MicroCFTA/Audit.lean"}
upstream_mismatches = []
for name in upstream:
    expected = subprocess.run(["git", "show", f"c0cc8a05:{name}"], cwd=root, check=True, capture_output=True).stdout
    if not (root / name).is_file() or (root / name).read_bytes() != expected:
        upstream_mismatches.append(name)

previous_file = root / "lean/restart-evidence/20261016-typing-do-seeded-worker/preservation-final.json"
previous = json.loads(previous_file.read_text())
manifests = list(previous["frozen_manifests"])
current_manifest = "lean/restart-evidence/20261016-drawn-fields-local-worker/frozen-modules.json"
current_present = (root / current_manifest).is_file()
if current_present:
    manifests.append(current_manifest)
frozen = {}
for name in manifests:
    entries = {path if "/" in path else f"lean/MicroCFTA/{path}.lean": expected for path, expected in json.loads((root / name).read_text()).items()}
    frozen[name] = {
        "checked": len(entries), "manifest_sha256": digest(root / name),
        "failures": [path for path, expected in entries.items() if not (root / path).is_file() or digest(root / path) != expected],
    }

old_findings = git("show", "e75e8c5c:FINDINGS.md")
historical = old_findings[old_findings.index("- **Negative typed-language bounds."):old_findings.index("## Current generator node views and source refresh")]
current_findings = (root / "FINDINGS.md").read_text()
registry_end = current_findings.index("## Current literal")
registry = current_findings[:registry_end]
audit_before = git("show", "66013b03:lean/MicroCFTA/Audit.lean")
audit_expected = audit_before.replace("import MicroCFTA.SourceCurrentAllocatedScanWorkerActual\n", "import MicroCFTA.SourceCurrentAllocatedScanWorkerActual\nimport MicroCFTA.SourceCurrentAllocatedLocalWorkerActual\n", 1)
package_roots = {"cfta", "cfta-generator", "cfta-ghc", "decision-model"}
package_files = {name for name in baseline if name.split("/", 1)[0] in package_roots}
current_packages = {name for name in git("ls-files").splitlines() if name.split("/", 1)[0] in package_roots}
report = {
    "baseline_files": len(baseline), "baseline_sha256": digest(baseline_file),
    "head": git("rev-parse", "HEAD").strip(), "source_main": git("rev-parse", "c0cc8a05").strip(),
    "source_merge": git("rev-parse", "896b0a1c").strip(),
    "missing": missing, "changed": changed, "allowed_restart_authorities": sorted(authorities),
    "allowed_upstream_diff": {"before": "5399d310", "after": "c0cc8a05", "paths": upstream},
    "upstream_file_mismatches": upstream_mismatches, "unexpected_changes": sorted(set(changed) - allowed),
    "older_non_audit_sources": len(proofs), "older_non_audit_changed": sorted(set(proofs) & set(changed)),
    "audit_only_adds_local_actual_import": (root / "lean/MicroCFTA/Audit.lean").read_text() == audit_expected,
    "active_package_tracked_files_before": len(package_files), "active_package_tracked_files_now": len(current_packages),
    "active_package_file_set_matches_upstream": package_files | set(upstream) == current_packages,
    "active_package_unexpected_changes": sorted(set(package_files) & set(changed) - set(upstream)),
    "all_starting_haskell_files": sum(name.endswith(".hs") for name in baseline),
    "upstream_haskell_paths": [name for name in upstream if name.endswith(".hs")],
    "previous_preservation_report_sha256": digest(previous_file), "current_frozen_manifest_pending": not current_present,
    "frozen_manifest_count": len(frozen), "frozen_module_entries": sum(item["checked"] for item in frozen.values()),
    "frozen_manifests": frozen,
    "stashes_unchanged": git("stash", "list", "--format=%H %gd %gs") == (evidence / "starting-stashes.txt").read_text(),
    "other_worktrees_unchanged": other_worktrees(git("worktree", "list", "--porcelain")) == other_worktrees((evidence / "starting-worktrees.txt").read_text()),
    "other_worktree_count": len(other_worktrees(git("worktree", "list", "--porcelain"))),
    "haskell_fix_registry_first": current_findings.startswith("# Current formalization findings\n\n## Haskell fix handoff for external work\n"),
    "historical_repair_block_reference": "e75e8c5c", "historical_repair_block_preserved": historical in registry,
    "historical_repair_block_sha256": hashlib.sha256(historical.encode()).hexdigest(),
    "upstream_recursive_field_repair_recorded": "b9219b9e" in registry and "FieldAtomOnDatatype" in registry,
    "status": git("status", "--short", "--branch"),
    "earlier_external_drafts": "Unavailable before this checkpoint. No recovery claim.",
}
(evidence / "preservation-final.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
assert len(baseline) == 5274 and len(proofs) == 2455
assert len(upstream) == 7 and len(report["upstream_haskell_paths"]) == 6
assert not missing and not report["unexpected_changes"] and not report["older_non_audit_changed"]
assert report["audit_only_adds_local_actual_import"] and not upstream_mismatches
assert report["active_package_file_set_matches_upstream"] and not report["active_package_unexpected_changes"]
assert len(frozen) == (27 if current_present else 26)
assert report["frozen_module_entries"] == (221 if current_present else 213)
assert all(not item["failures"] for item in frozen.values())
assert not current_present or frozen[current_manifest]["checked"] == 8
assert report["stashes_unchanged"] and report["other_worktrees_unchanged"]
assert report["haskell_fix_registry_first"] and report["historical_repair_block_preserved"]
assert report["upstream_recursive_field_repair_recorded"]
assert not args.require_current or current_present
