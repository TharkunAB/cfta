"""Verify the typing-do refresh and current seeded and Scan checkpoint."""

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
    return subprocess.run(
        ["git", *arguments], cwd=root, check=True, text=True, capture_output=True
    ).stdout


def other_worktrees(text: str) -> list[str]:
    return [
        block for block in text.strip().split("\n\n")
        if not block.startswith(f"worktree {root}\n")
    ]


baseline_file = evidence / "starting-sha256.json"
baseline = json.loads(baseline_file.read_text())
missing = sorted(name for name in baseline if not (root / name).is_file())
changed = sorted(
    name for name, expected in baseline.items()
    if (root / name).is_file() and digest(root / name) != expected
)
authorities = {
    "NEXT-PROMPT.md", "HANDOFF.md", "FINDINGS.md", "lean/README.md",
    "lean/SYSTEM.md", "lean/API-COVERAGE.md", "lean/COVERAGE.md",
}
upstream = git("diff", "--name-only", "999c04a5", "5399d310").splitlines()
proofs = [
    name for name in baseline
    if name.startswith("lean/MicroCFTA/") and name.endswith(".lean")
    and name != "lean/MicroCFTA/Audit.lean"
]
previous_file = root / "lean/restart-evidence/20261016-frontend-node-view-refresh/preservation-final.json"
previous = json.loads(previous_file.read_text())
manifests = list(previous["frozen_manifests"])
current_manifest = "lean/restart-evidence/20261016-typing-do-seeded-worker/frozen-modules.json"
current_present = (root / current_manifest).is_file()
if current_present:
    manifests.append(current_manifest)
frozen = {}
for name in manifests:
    entries = {
        path if "/" in path else f"lean/MicroCFTA/{path}.lean": expected
        for path, expected in json.loads((root / name).read_text()).items()
    }
    frozen[name] = {
        "checked": len(entries), "manifest_sha256": digest(root / name),
        "failures": [
            path for path, expected in entries.items()
            if not (root / path).is_file() or digest(root / path) != expected
        ],
    }
upstream_mismatches = []
for name in upstream:
    expected = subprocess.run(
        ["git", "show", f"5399d310:{name}"], cwd=root, check=True, capture_output=True
    ).stdout
    if not (root / name).is_file() or (root / name).read_bytes() != expected:
        upstream_mismatches.append(name)

old_findings = git("show", "e75e8c5c:FINDINGS.md")
historical_start = old_findings.index("- **Negative typed-language bounds.")
historical_end = old_findings.index("## Current generator node views and source refresh")
historical = old_findings[historical_start:historical_end]
current_findings = (root / "FINDINGS.md").read_text()
headings = [
    "## Current literal seeded queries and class scanning",
    "## Current generator node views and source refresh",
]
registry = current_findings[:min(current_findings.index(heading) for heading in headings if heading in current_findings)]
registry_first = current_findings.startswith(
    "# Current formalization findings\n\n## Haskell fix handoff for external work\n"
)
historical_preserved = historical in registry
package_roots = {"cfta", "cfta-generator", "cfta-ghc", "decision-model"}
package_files = {name for name in baseline if name.split("/", 1)[0] in package_roots}
current_packages = {
    name for name in git("ls-files").splitlines() if name.split("/", 1)[0] in package_roots
}
allowed = authorities | set(upstream) | {"lean/MicroCFTA/Audit.lean"}
report = {
    "baseline_files": len(baseline), "baseline_sha256": digest(baseline_file),
    "head": git("rev-parse", "HEAD").strip(),
    "source_main": git("rev-parse", "5399d310").strip(),
    "source_merge": git("rev-parse", "82d47236").strip(),
    "missing": missing, "changed": changed,
    "allowed_restart_authorities": sorted(authorities),
    "allowed_upstream_diff": {"before": "999c04a5", "after": "5399d310", "paths": upstream},
    "upstream_file_mismatches": upstream_mismatches,
    "unexpected_changes": sorted(set(changed) - allowed),
    "older_non_audit_sources": len(proofs),
    "older_non_audit_changed": sorted(set(proofs) & set(changed)),
    "audit_additions": "Two imports: SeededWorkerActual and ScanWorkerActual.",
    "active_package_tracked_files_before": len(package_files),
    "active_package_tracked_files_now": len(current_packages),
    "active_package_file_set_matches_upstream": package_files | set(upstream) == current_packages,
    "active_package_unexpected_changes": sorted(set(package_files) & set(changed) - set(upstream)),
    "all_starting_haskell_files": sum(name.endswith(".hs") for name in baseline),
    "upstream_haskell_paths": [name for name in upstream if name.endswith(".hs")],
    "previous_preservation_report_sha256": digest(previous_file),
    "current_frozen_manifest_pending": not current_present,
    "frozen_manifest_count": len(frozen),
    "frozen_module_entries": sum(entry["checked"] for entry in frozen.values()),
    "frozen_manifests": frozen,
    "stashes_unchanged": git("stash", "list", "--format=%H %gd %gs")
        == (evidence / "starting-stashes.txt").read_text(),
    "other_worktrees_unchanged": other_worktrees(git("worktree", "list", "--porcelain"))
        == other_worktrees((evidence / "starting-worktrees.txt").read_text()),
    "other_worktree_count": len(other_worktrees(git("worktree", "list", "--porcelain"))),
    "haskell_fix_registry_first": registry_first,
    "haskell_fix_registry_reference": "e75e8c5c",
    "repair_and_counterexample_block_sha256": hashlib.sha256(historical.encode()).hexdigest(),
    "repair_and_counterexample_block_preserved": historical_preserved,
    "negative_bound_fix_recorded": "- **Negative typed-language bounds." in registry,
    "recursive_field_gap_recorded": "- **Recursive field-pool invariant: confirmed, unfixed." in registry,
    "status": git("status", "--short", "--branch"),
    "earlier_external_drafts": "Unavailable before this checkpoint. No recovery or reverification claim.",
}
(evidence / "preservation-final.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
assert len(baseline) == 5135 and len(proofs) == 2443
assert len(upstream) == 5 and len(report["upstream_haskell_paths"]) == 3
assert not missing and not report["unexpected_changes"]
assert not report["older_non_audit_changed"]
assert not upstream_mismatches and not report["active_package_unexpected_changes"]
assert report["active_package_file_set_matches_upstream"]
assert len(frozen) == (26 if current_present else 25)
assert report["frozen_module_entries"] == (213 if current_present else 201)
assert all(not entry["failures"] for entry in frozen.values())
assert not current_present or frozen[current_manifest]["checked"] == 12
assert report["stashes_unchanged"] and report["other_worktrees_unchanged"]
assert registry_first and historical_preserved and report["negative_bound_fix_recorded"]
assert report["recursive_field_gap_recorded"]
assert not args.require_current or current_present
