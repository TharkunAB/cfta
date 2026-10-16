"""Check input-derived native query budgets and prefix capacity."""

import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


modules = json.loads((evidence / "frozen-modules.json").read_text())
assert len(modules) == 6
public = (evidence / "all-public.lean").read_text()
declarations = set()
for module, expected in modules.items():
    source = root / f"lean/MicroCFTA/{module}.lean"
    assert digest(source) == expected, source
    assert digest(evidence / f"{module}.lean") == expected, module
    namespaces = []
    for line in source.read_text().splitlines():
        namespace = re.match(r"^namespace (\S+)\s*$", line)
        if namespace:
            namespaces.append(namespace[1])
            continue
        ending = re.match(r"^end (\S+)\s*$", line)
        if ending:
            assert namespaces[-1] == ending[1], (module, line, namespaces)
            namespaces.pop()
            continue
        declaration = re.match(r"^[ \t]*(?:noncomputable )?(?:theorem|def|structure|inductive|abbrev) ([A-Za-z_][A-Za-z_0-9.]*)", line)
        if declaration:
            name = ".".join(namespaces + [declaration[1]])
            assert f"#print axioms {name}\n" in public, name
            assert f"#check @{name}\n" in public, name
            declarations.add(name)
    assert not namespaces
assert len(declarations) == 75

kernel_logs = json.loads((evidence / "kernel-logs.json").read_text())
allowed = {"propext", "Classical.choice", "Quot.sound"}
final_logs = ["all-public-1.log", *kernel_logs.values()]
for name in final_logs:
    text = (evidence / name).read_text()
    assert not re.search(r"error:|warning:|sorryAx", text), name
    for found in re.findall(r"depends on axioms: \[(.*?)\]", text, re.S):
        assert {axiom.strip().split(".{", 1)[0] for axiom in found.split(",")} <= allowed, (name, found)
assert all(name in (evidence / "all-public-1.log").read_text() for name in declarations)

kernel_count = 0
for source, log in kernel_logs.items():
    text = (evidence / source).read_text()
    printed = re.findall(r"^#print axioms (\S+)", text, re.M)
    checked = re.findall(r"^#check @(\S+)", text, re.M)
    assert printed == checked and printed, source
    kernel_count += len(printed)
    assert all(name in (evidence / log).read_text() for name in printed), log
assert kernel_count == 20, kernel_count

manifest_entries = 0


def check_entries(value):
    global manifest_entries
    if isinstance(value, dict):
        if isinstance(value.get("path"), str) and isinstance(value.get("sha256"), str):
            path = root / value["path"]
            assert path.is_file() and digest(path) == value["sha256"], path
            manifest_entries += 1
        for item in value.values():
            check_entries(item)
    elif isinstance(value, list):
        for item in value:
            check_entries(item)


manifests = {}
for path in sorted(evidence.glob("*-manifest.json")):
    check_entries(json.loads(path.read_text()))
    manifests[path.name] = digest(path)

audit = (evidence / "audit-1.log").read_text()
assert "Build completed successfully (2562 jobs)." in audit
match = re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems\.", audit)
assert match
report = {
    "result": "PASS", "frozen_modules": len(modules),
    "declared_public_pairs": len(declarations), "integration_pairs": kernel_count,
    "allowed_axioms": sorted(allowed), "audit_jobs": 2562,
    "audit_dependency_checks": int(match[1]), "audit_log_sha256": digest(evidence / "audit-1.log"),
    "final_probe_logs": {name: digest(evidence / name) for name in final_logs},
    "checked_component_manifest_entries": manifest_entries, "component_manifests": manifests,
    "completion_boundary": "Original operand profiles compute constructor request budgets for every finite yielded native node and edge query prefix. Initial supplies plus that budget derive prefix capacity.",
    "remaining": "Output row and arity envelopes; cumulative outer reduction reservation budgets; general recursive progress, repeated passes, frontends, concrete runtime, and full pipeline.",
}
(evidence / "checkpoint-validation.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
