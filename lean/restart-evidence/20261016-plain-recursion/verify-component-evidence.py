"""Verify current components and the exact snapshots named by draft reviews."""

import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
historical = {
    ("recursion-review-manifest.json", "lean/MicroCFTA/SourceCurrentAllocatedPartialPlainRows.lean"):
        evidence / "recursion-review-initial-PlainRows.lean",
    ("terminal-node-reviewed-hashes.json", "lean/MicroCFTA/SourceCurrentAllocatedPartialPlainNode.lean"):
        evidence / "recursion-review-draft-PlainNode.lean",
}
reports = {}
manifests = sorted(evidence.glob("*-manifest.json")) + [evidence / "terminal-node-reviewed-hashes.json"]
for manifest in manifests:
    data = json.loads(manifest.read_text())
    entries = {}
    labels = {}
    for key in ("source_sha256", "sources_sha256", "evidence_sha256"):
        if isinstance(data.get(key), dict):
            for name, expected in data[key].items():
                (entries if "/" in name else labels)[name] = expected
    for item in data.get("files", []):
        entries[item["path"]] = item["sha256"]
    for item in data.get("sources", []):
        entries[item.get("snapshot") or item.get("path") or item["source"]] = item["sha256"]
    for item in data.get("artifacts", []):
        entries[item["path"]] = item["sha256"]
    if isinstance(data.get("review"), dict):
        entries[data["review"]["path"]] = data["review"]["sha256"]
    if isinstance(data.get("source_sha256"), str) and "source" in data:
        entries[data["source"]] = data["source_sha256"]
    if "review_sha256" in data:
        review = manifest.with_name(manifest.name.replace("-manifest.json", ".md"))
        entries[str(review.relative_to(root))] = data["review_sha256"]
    resolved = []
    failures = []
    for name, expected in entries.items():
        path = historical.get((manifest.name, name), root / name)
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            failures.append(name)
        if (manifest.name, name) in historical:
            resolved.append({"reviewed_source": name, "snapshot": str(path.relative_to(root)), "sha256": expected})
    assert all(expected in entries.values() for expected in labels.values()), manifest.name
    reports[manifest.name] = {"entries": len(entries), "historical_snapshots": resolved, "failures": failures}
    assert entries and not failures, reports[manifest.name]

logs = ["prefixes-checks-2.log", "children-checks-2.log", "terminal-checks-3.log",
        "rows-review-checks-2.log", "node-review-public.log", "node-review-kernels-1.log",
        "root-review-checks-3.log"]
for name in logs:
    assert not re.search(r"\b(?:warning|error):|sorryAx", (evidence / name).read_text()), name

report = {"manifests": reports, "component_hash_entries": sum(item["entries"] for item in reports.values()),
          "final_probe_logs": logs, "public_declaration_pairs": 16, "integration_kernel_pairs": 23,
          "final_probe_errors_warnings_or_sorryAx": False}
(evidence / "component-verification.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
