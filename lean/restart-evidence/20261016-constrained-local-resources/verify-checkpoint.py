"""Check local and parent initial resources and capacity adapters."""

import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


modules = json.loads((evidence / "frozen-modules.json").read_text())
assert len(modules) == 11
public = (evidence / "all-public.lean").read_text()
declarations = set()
for module, expected in modules.items():
    source = root / f"lean/MicroCFTA/{module}.lean"
    assert digest(source) == expected, source
    assert digest(evidence / f"{module}.lean") == expected, module
    namespaces = []
    sections = []
    for line in source.read_text().splitlines():
        namespace = re.match(r"^namespace (\S+)\s*$", line)
        if namespace:
            namespaces.append(namespace[1])
            continue
        section = re.match(r"^section (\S+)\s*$", line)
        if section:
            sections.append(section[1])
            continue
        ending = re.match(r"^end (\S+)\s*$", line)
        if ending and sections and sections[-1] == ending[1]:
            sections.pop()
            continue
        if ending:
            assert namespaces[-1] == ending[1], (module, line, namespaces)
            namespaces.pop()
            continue
        declaration = re.match(r"^[ \t]*(?:noncomputable )?(?:theorem|def|structure|inductive|abbrev) ([^\s({:]+)", line)
        if declaration:
            name = ".".join(namespaces + [declaration[1]])
            assert f"#print axioms {name}\n" in public, name
            assert f"#check @{name}\n" in public, name
            declarations.add(name)
    assert not namespaces and not sections
assert len(declarations) == 35
printed = re.findall(r"^#print axioms (\S+)", public, re.M)
checked = re.findall(r"^#check @(\S+)", public, re.M)
assert printed == checked and len(set(printed)) == 35
assert set(printed) == declarations == set(json.loads((evidence / "public-declarations.json").read_text()))
for name in ["all-public-1.log", "all-integration-2.log"]:
    assert not re.search("[⋯…]", (evidence / name).read_text()), name
combined = (evidence / "all-integration.lean").read_text()
printed_integration = re.findall(r"^#print axioms (\S+)", combined, re.M)
checked_integration = re.findall(r"^#check @(\S+)", combined, re.M)
assert printed_integration == checked_integration == json.loads((evidence / "integration-declarations.json").read_text())
assert len(printed_integration) == 20
assert all(name in (evidence / "all-integration-2.log").read_text() for name in printed_integration)

kernel_logs = json.loads((evidence / "kernel-logs.json").read_text())
allowed = {"propext", "Classical.choice", "Quot.sound"}
final_logs = ["all-public-1.log", "all-integration-2.log", *kernel_logs.values()]
for name in final_logs:
    text = (evidence / name).read_text()
    assert not re.search(r"error(?:\(|:)|warning(?:\(|:)|sorryAx", text), name
    for found in re.findall(r"depends on axioms: \[(.*?)\]", text, re.S):
        assert {axiom.strip().split(".{", 1)[0] for axiom in found.split(",")} <= allowed, (name, found)
assert all(name.replace("«", "").replace("»", "") in (evidence / "all-public-1.log").read_text() for name in declarations)

kernel_count = 0
for source, log in kernel_logs.items():
    text = (evidence / source).read_text()
    printed = re.findall(r"^#print axioms (\S+)", text, re.M)
    checked = re.findall(r"^#check @?(\S+)", text, re.M)
    assert printed == checked and printed, source
    kernel_count += len(printed)
    assert all(name in (evidence / log).read_text() for name in printed), log
assert kernel_count == json.loads((evidence / "integration-count.json").read_text()) == 20, kernel_count

manifest_entries = 0
historical_entries = 0
historical = {}
for entry in json.loads((evidence / "historical-snapshots.json").read_text()):
    assert entry["original_path"].startswith("lean/restart-evidence/20261016-constrained-local-resources/")
    snapshot = root / entry["snapshot"]
    assert snapshot.is_file() and digest(snapshot) == entry["sha256"], snapshot
    historical[(entry["original_path"], entry["sha256"])] = snapshot


def check_entries(value):
    global manifest_entries, historical_entries
    if isinstance(value, dict):
        if isinstance(value.get("path"), str) and isinstance(value.get("sha256"), str):
            path = root / value["path"]
            if not path.is_file() or digest(path) != value["sha256"]:
                assert (value["path"], value["sha256"]) in historical, path
                historical_entries += 1
            manifest_entries += 1
        for item in value.values():
            check_entries(item)
    elif isinstance(value, list):
        for item in value:
            check_entries(item)


manifests = {}
for path in sorted([*evidence.glob("*-manifest.json"), *evidence.glob("*-reviewed-hashes.json")]):
    check_entries(json.loads(path.read_text()))
    manifests[path.name] = digest(path)



audit = (evidence / "audit-1.log").read_text()
assert "Build completed successfully (2621 jobs)." in audit
match = re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems\.", audit)
assert match and int(match[1]) == 60599
report = {
    "result": "PASS", "frozen_modules": len(modules),
    "declared_public_pairs": len(declarations), "integration_pairs": kernel_count,
    "allowed_axioms": sorted(allowed), "audit_jobs": 2621,
    "audit_dependency_checks": int(match[1]), "audit_log_sha256": digest(evidence / "audit-1.log"),
    "final_probe_logs": {name: digest(evidence / name) for name in final_logs},
    "checked_component_manifest_entries": manifest_entries, "historical_snapshot_entries": historical_entries, "component_manifests": manifests,
    "completion_boundary": "Constructed finite ordinary Required/Pass stage, local, parent and full caller resources retain existing semantic receipts, strict Reads, stable literal execution, causal profiles, Work and capacity from initial-only headroom. Existing edit/class/pass/stage/local/resident-parent capacity plans are derived from initial budgets by exact earlier-return uniqueness.",
    "remaining": "Whole outer quantitative returned-cache certificates, constraint envelopes, cumulative constructor accounting and initial root headroom that derives every reached ParentCapacity; other resource families; general recursive progress, repeated passes, current frontends, concrete Haskell, and full pipelines.",
}
(evidence / "checkpoint-validation.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
