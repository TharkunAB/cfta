"""Verify current conjunction checkpoint bytes and the complete repair registry prefix."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--require-current", action="store_true")
parser.add_argument("--output", default="preservation-final.json")
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


def repair_block(text: str) -> str:
    headings = ("## Current literal conjunction execution and full caller receipts",
                "## Current literal checked edits and class passes",
                "## Current source refresh and literal merge execution",
                "## Current literal checked targets and shared leaves")
    end = min(text.index(heading) for heading in headings if heading in text)
    return text[:end]


baseline_file = evidence / "starting-sha256.json"
baseline = json.loads(baseline_file.read_text())
missing = sorted(name for name in baseline if not (root / name).is_file())
changed = sorted(
    name for name, expected in baseline.items()
    if (root / name).is_file() and digest(root / name) != expected
)
proofs = [
    name for name in baseline
    if name.startswith("lean/MicroCFTA/")
    and name.endswith(".lean")
    and name != "lean/MicroCFTA/Audit.lean"
]
authorities = {
    "NEXT-PROMPT.md", "HANDOFF.md", "FINDINGS.md", "lean/README.md",
    "lean/SYSTEM.md", "lean/API-COVERAGE.md", "lean/COVERAGE.md",
}
upstream: list[str] = []
allowed = authorities | {"lean/MicroCFTA/Audit.lean"} | set(upstream)
previous_file = root / "lean/restart-evidence/20261016-current-edit-worker/preservation-final.json"
previous = json.loads(previous_file.read_text())
manifests = list(previous["frozen_manifests"])
previous_manifest_count = len(manifests)
current_manifest = "lean/restart-evidence/20261016-current-conjunction-worker/frozen-modules.json"
current_present = (root / current_manifest).is_file()
if current_present:
    manifests.append(current_manifest)
frozen = {}
for name in manifests:
    stored = json.loads((root / name).read_text())
    entries = {
        path if "/" in path else f"lean/MicroCFTA/{path}.lean": expected
        for path, expected in stored.items()
    }
    failures = [
        path for path, expected in entries.items()
        if not (root / path).is_file() or digest(root / path) != expected
    ]
    frozen[name] = {
        "checked": len(entries), "manifest_sha256": digest(root / name), "failures": failures
    }

old_block = repair_block(git("show", "ebf92715:FINDINGS.md"))
current_block = repair_block((root / "FINDINGS.md").read_text())
repair_titles = [
    line.split("**", 2)[1]
    for line in old_block.splitlines() if line.startswith("- **")
]
upstream_mismatches = []
for name in upstream:
    expected = subprocess.run(
        ["git", "show", f"ccebf0f7:{name}"], cwd=root, check=True, capture_output=True
    ).stdout
    path = root / name
    if not path.is_file() or path.read_bytes() != expected:
        upstream_mismatches.append(name)

package_roots = {"cfta", "cfta-generator", "cfta-ghc", "decision-model"}
package_files = sorted(name for name in baseline if name.split("/", 1)[0] in package_roots)
package_mismatches = sorted(name for name in package_files if name in missing or name in changed)
tracked = set(git("ls-files").splitlines())
current_package_files = sorted(name for name in tracked if name.split("/", 1)[0] in package_roots)
haskell_files = sorted(name for name in baseline if name.endswith(".hs"))
haskell_mismatches = sorted(name for name in haskell_files if name in missing or name in changed)

report = {
    "baseline_files": len(baseline),
    "baseline_sha256": digest(baseline_file),
    "missing": missing,
    "changed": changed,
    "allowed_restart_authorities": sorted(authorities),
    "allowed_audit": "lean/MicroCFTA/Audit.lean",
    "allowed_upstream_diff": {"before": "ccebf0f7", "after": "ccebf0f7", "paths": upstream},
    "upstream_file_mismatches": upstream_mismatches,
    "active_package_roots": sorted(package_roots),
    "active_package_tracked_file_count": len(package_files),
    "active_package_haskell_file_count": sum(name.endswith(".hs") for name in package_files),
    "active_package_files_sha256": hashlib.sha256(("\n".join(package_files) + "\n").encode()).hexdigest(),
    "active_package_file_set_unchanged": current_package_files == package_files,
    "active_package_file_mismatches": package_mismatches,
    "all_tracked_haskell_files": len(haskell_files),
    "all_tracked_haskell_mismatches": haskell_mismatches,
    "unexpected_changes": sorted(set(changed) - allowed),
    "older_non_audit_sources": len(proofs),
    "older_non_audit_missing": sorted(set(proofs) & set(missing)),
    "older_non_audit_changed": sorted(set(proofs) & set(changed)),
    "previous_preservation_report_sha256": digest(previous_file),
    "previous_frozen_manifest_count": previous_manifest_count,
    "current_frozen_manifest_pending": not current_present,
    "frozen_manifest_count": len(frozen),
    "frozen_module_entries": sum(entry["checked"] for entry in frozen.values()),
    "frozen_manifests": frozen,
    "stashes_unchanged": git("stash", "list", "--format=%H %gd %gs")
        == (evidence / "starting-stashes.txt").read_text(),
    "other_worktrees_unchanged": other_worktrees(git("worktree", "list", "--porcelain"))
        == other_worktrees((evidence / "starting-worktrees.txt").read_text()),
    "other_worktree_count": len(other_worktrees(git("worktree", "list", "--porcelain"))),
    "haskell_fix_registry_reference": git("rev-parse", "ebf92715").strip(),
    "haskell_fix_registry_rule": "Exact full ebf92715 FINDINGS prefix before Current literal checked edits and class passes equals current prefix before Current literal conjunction execution and full caller receipts. This includes registry metadata, four repair bullets, and PR 55 handoff.",
    "haskell_fix_registry_titles": repair_titles,
    "haskell_fix_registry_old_sha256": hashlib.sha256(old_block.encode()).hexdigest(),
    "haskell_fix_registry_current_sha256": hashlib.sha256(current_block.encode()).hexdigest(),
    "haskell_fix_registry_preserved": old_block == current_block,
    "status": git("status", "--short", "--branch"),
    "head": git("rev-parse", "HEAD").strip(),
    "earlier_external_drafts": "Unavailable before this checkpoint. No recovery or reverification claim.",
}
(evidence / args.output).write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
assert len(baseline) == 4977 and len(proofs) == 2433
assert not upstream and previous_manifest_count == 24
assert not missing and not report["unexpected_changes"]
assert not report["older_non_audit_changed"]
assert not upstream_mismatches and not package_mismatches and not haskell_mismatches
assert report["active_package_file_set_unchanged"]
assert not current_present or frozen[current_manifest]["checked"] == 10
assert all(not entry["failures"] for entry in frozen.values())
assert report["stashes_unchanged"] and report["other_worktrees_unchanged"]
assert len(repair_titles) == 4 and report["haskell_fix_registry_preserved"]
assert not args.require_current or current_present
