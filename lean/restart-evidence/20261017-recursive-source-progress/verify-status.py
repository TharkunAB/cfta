"""Check the source and evidence used by the proof status note."""

import hashlib
import json
import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = Path(__file__).resolve().parent


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True)


def other_worktrees(text: str) -> list[str]:
    return [block for block in text.strip().split("\n\n") if not block.startswith(f"worktree {ROOT}\n")]


baseline: dict[str, str] = json.loads((EVIDENCE / "starting-sha256.json").read_text())
missing = [name for name in baseline if not (ROOT / name).is_file()]
changed = [name for name, expected in baseline.items() if (ROOT / name).is_file() and digest(ROOT / name) != expected]
allowed = {"NEXT-PROMPT.md", "HANDOFF.md", "FINDINGS.md", "lean/README.md"}
proofs = [name for name in baseline if name.startswith("lean/MicroCFTA/") and name.endswith(".lean")]
haskell = [name for name in baseline if name.endswith(".hs")]
validation_dir = ROOT / "lean/restart-evidence/20261016-drawn-fields-local-worker"
validation = json.loads((validation_dir / "source-validation-inputs.json").read_text())
source_failures = [name for name, expected in validation["source_hashes"].items() if digest(ROOT / name) != expected]
repro = ROOT / validation["historical_repro"]
repro_matches = digest(repro) == validation["historical_repro_sha256"]
prior_dir = ROOT / "lean/restart-evidence/20261017-outer-raw-reach-capacity"
prior = json.loads((prior_dir / "preservation-final.json").read_text())
frozen_failures: list[str] = []
frozen_entries = 0
for manifest, record in prior["frozen_manifests"].items():
    manifest_path = ROOT / manifest
    if digest(manifest_path) != record["manifest_sha256"]:
        frozen_failures.append(manifest)
    entries: dict[str, str] = json.loads(manifest_path.read_text())
    frozen_entries += len(entries)
    for name, expected in entries.items():
        path = ROOT / (name if "/" in name else f"lean/MicroCFTA/{name}.lean")
        if digest(path) != expected:
            frozen_failures.append(str(path.relative_to(ROOT)))

old_findings = git("show", "e75e8c5c:FINDINGS.md")
historical = old_findings[old_findings.index("- **Negative typed-language bounds."):old_findings.index("## Current generator node views and source refresh")]
findings = (ROOT / "FINDINGS.md").read_text()
review_failures: list[str] = []
review_entries = 0
for name in ("recursive-semantic-progress-manifest.json", "recursive-allocated-progress-manifest.json", "recursive-boundary-manifest.json"):
    manifest = json.loads((EVIDENCE / name).read_text())
    entries = manifest.get("entries", manifest.get("files", []))
    review_entries += len(entries)
    for entry in entries:
        if digest(ROOT / entry["path"]) != entry["sha256"]:
            review_failures.append(entry["path"])
source_manifest = json.loads((EVIDENCE / "recursive-semantic-progress-source-hashes.json").read_text())
for entry in source_manifest["sources"]:
    if digest(ROOT / entry["path"]) != entry["sha256"]:
        review_failures.append(entry["path"])

probe_counts: dict[str, int] = {}
probe_failures: list[str] = []
axioms: set[str] = set()
for name, log_name, expected in (
    ("recursive-semantic-progress-public.lean", "recursive-semantic-progress-public.log", 15),
    ("recursive-semantic-progress-kernels.lean", "recursive-semantic-progress-kernels-1.log", 3),
    ("recursive-allocated-progress-public.lean", "recursive-allocated-progress-public-1.log", 11),
):
    source = (EVIDENCE / name).read_text()
    log = (EVIDENCE / log_name).read_text()
    count = len(re.findall(r"^#print axioms ", source, re.MULTILINE))
    answers = len(re.findall(r"^'[^']+' (?:depends on axioms:|does not depend on any axioms)", log, re.MULTILINE))
    signatures = len(re.findall(r"^#check ", source, re.MULTILINE))
    probe_counts[name] = count
    if count != expected or answers != expected or signatures != expected:
        probe_failures.append(f"{name}: pair count mismatch {count}/{answers}/{signatures}/{expected}")
    if re.search(r"warning:|error:|sorryAx|\[truncated\]|…|⋯", log):
        probe_failures.append(f"{log_name}: diagnostic or omission marker")
    for group in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", log):
        for token in group.split(","):
            axiom = re.sub(r"\.\{[^}]*\}", "", token).strip()
            if axiom:
                axioms.add(axiom)
    if not axioms <= {"propext", "Classical.choice", "Quot.sound"}:
        probe_failures.append(f"{log_name}: unexpected axiom")
probe_result = json.loads((EVIDENCE / "recursive-probe-results.json").read_text())
probe_log = (EVIDENCE / probe_result["final_log"]).read_text()
checks = {
    "no_starting_file_removed": not missing,
    "only_status_authorities_changed": set(changed) <= allowed,
    "all_lean_proofs_and_audit_unchanged": not set(proofs).intersection(changed),
    "all_haskell_unchanged": not set(haskell).intersection(changed),
    "validated_haskell_source_matches": not source_failures,
    "historical_reproducer_matches": repro_matches,
    "frozen_production_manifests_and_sources_match": not frozen_failures,
    "historical_repair_block_preserved": historical in findings,
    "repair_handoff_first": findings.startswith("# Current formalization findings\n\n## Haskell fix handoff for external work\n"),
    "repair_and_recheck_recorded": all(value in findings[:findings.index("- **Negative typed-language bounds.")] for value in ("b9219b9e", "FieldAtomOnDatatype", "Status rechecked on 2026-10-17")),
    "stashes_unchanged": git("stash", "list", "--format=%H %gd %gs") == (EVIDENCE / "starting-stashes.txt").read_text(),
    "other_worktrees_unchanged": other_worktrees(git("worktree", "list", "--porcelain")) == other_worktrees((EVIDENCE / "starting-worktrees.txt").read_text()),
    "review_hashes_match": not review_failures,
    "imported_axioms_and_full_signatures_pass": not probe_failures,
    "four_focused_source_checks_pass": probe_result["final_exit"] == 0 and probe_result["checks"] == 4 and probe_log.count("Just True") == 4 and not re.search(r"warning:|error:|Just False", probe_log),
}
report = {
    "checked_head": git("rev-parse", "HEAD").strip(),
    "starting_files": len(baseline),
    "non_audit_proofs": len(proofs) - 1,
    "haskell_files": len(haskell),
    "changed": changed,
    "missing": missing,
    "frozen_manifests": len(prior["frozen_manifests"]),
    "frozen_entries": frozen_entries,
    "source_validation_failures": source_failures,
    "frozen_failures": frozen_failures,
    "review_entries": review_entries,
    "review_failures": review_failures,
    "probe_pairs": probe_counts,
    "axioms": sorted(axioms),
    "probe_failures": probe_failures,
    "reused_audit": "20261017-outer-raw-reach-capacity",
    "new_theorems": 0,
    "new_full_build_claimed": False,
    "checks": checks,
}
(EVIDENCE / "status-verification.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"checks": checks, "files": len(baseline), "proofs": len(proofs) - 1, "haskell": len(haskell), "frozen": [len(prior["frozen_manifests"]), frozen_entries]}, indent=2))
raise SystemExit(0 if all(checks.values()) else 1)
