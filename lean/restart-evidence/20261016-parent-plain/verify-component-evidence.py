"""Check frozen component source and evidence hashes for this checkpoint."""

import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
reports = {}
for manifest in sorted(evidence.glob("*-manifest.json")):
    data = json.loads(manifest.read_text())
    entries = {}
    for key in ("source_sha256", "sources_sha256", "evidence_sha256"):
        if isinstance(data.get(key), dict):
            entries.update(data[key])
    for item in data.get("files", []):
        entries[item["path"]] = item["sha256"]
    if isinstance(data.get("source_sha256"), str) and "source" in data:
        entries[data["source"]] = data["source_sha256"]
    if "review_sha256" in data:
        entries[str(manifest.with_name(manifest.name.replace("-manifest.json", ".md")).relative_to(root))] = data["review_sha256"]
    failures = [name for name, expected in entries.items()
                if not (root / name).is_file()
                or hashlib.sha256((root / name).read_bytes()).hexdigest() != expected]
    reports[manifest.name] = {"entries": len(entries), "failures": failures}
    assert entries and not failures, reports[manifest.name]

checksum_entries = 0
for checksums in sorted(evidence.glob("*-SHA256SUMS")):
    for line in checksums.read_text().splitlines():
        expected, name = line.split(maxsplit=1)
        assert hashlib.sha256((root / name.strip()).read_bytes()).hexdigest() == expected, name
        checksum_entries += 1

logs = ["localplain-ranges-probes-1.log", "domain-review-public-final.log",
        "domain-review-kernels-final.log", "parent-checks-5.log", "inputs-probes-1.log",
        "edgecall-review-public-final.log", "edgecall-review-kernels-final.log"]
for name in logs:
    assert not re.search(r"\b(?:warning|error):|sorryAx", (evidence / name).read_text()), name

report = {"manifests": reports, "component_hash_entries": sum(item["entries"] for item in reports.values()),
          "checksum_entries": checksum_entries, "final_probe_logs": logs,
          "public_axiom_signature_pairs": 28, "integration_kernel_pairs": 25,
          "final_probe_errors_warnings_or_sorryAx": False}
(evidence / "component-verification.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
