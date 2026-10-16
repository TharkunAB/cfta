"""Verify the retained repository sources and frozen proof manifests."""

import hashlib
import json
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, check=True, text=True, capture_output=True
    ).stdout


baseline = json.loads((evidence / "starting-sha256.json").read_text())
missing = [name for name in baseline if not (root / name).is_file()]
changed = [
    name for name, expected in baseline.items()
    if (root / name).is_file() and digest(root / name) != expected
]
proofs = [
    name for name in baseline
    if name.startswith("lean/MicroCFTA/")
    and name.endswith(".lean")
    and name != "lean/MicroCFTA/Audit.lean"
]
allowed = {
    "NEXT-PROMPT.md", "HANDOFF.md", "FINDINGS.md", "lean/README.md",
    "lean/SYSTEM.md", "lean/API-COVERAGE.md", "lean/COVERAGE.md",
    "lean/MicroCFTA/Audit.lean",
}
previous = json.loads(
    (root / "lean/restart-evidence/20261016-current-scan-memos/preservation-final.json").read_text()
)
manifests = list(previous["frozen_manifests"])
manifests.append("lean/restart-evidence/20261016-checked-merge/frozen-modules.json")
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
    frozen[name] = {"checked": len(entries), "failures": failures}


def other_worktrees(text: str) -> list[str]:
    return [
        block for block in text.strip().split("\n\n")
        if not block.startswith(f"worktree {root}\n")
    ]


old_findings = git("show", "b7510ec5:FINDINGS.md")
registry_start = "## Haskell fix handoff for external work\n"
registry_end = "## Current checked Scan global memos and selected required execution\n"
registry = old_findings.split(registry_start, 1)[1].split(registry_end, 1)[0]
current_registry = (root / "FINDINGS.md").read_text().split(registry_start, 1)[1]
report = {
    "baseline_files": len(baseline),
    "missing": missing,
    "changed": changed,
    "unexpected_changes": sorted(set(changed) - allowed),
    "older_non_audit_sources": len(proofs),
    "older_non_audit_changed": sorted(set(proofs) & set(changed)),
    "frozen_manifests": frozen,
    "stashes_unchanged": git("stash", "list", "--format=%H %gd %gs")
        == (evidence / "starting-stashes.txt").read_text(),
    "other_worktrees_unchanged": other_worktrees(git("worktree", "list", "--porcelain"))
        == other_worktrees((evidence / "starting-worktrees.txt").read_text()),
    "haskell_fix_registry_preserved": current_registry.startswith(registry),
    "earlier_external_drafts": "Unavailable before this checkpoint. No recovery or reverification claim.",
}
(evidence / "preservation-final.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
assert not missing and not report["unexpected_changes"]
assert not report["older_non_audit_changed"]
assert all(not entry["failures"] for entry in frozen.values())
assert report["stashes_unchanged"] and report["other_worktrees_unchanged"]
assert report["haskell_fix_registry_preserved"]
