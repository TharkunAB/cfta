"""Check finite ordinary outer completion and its explicit range boundary."""

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
public_text = (evidence / "all-public.lean").read_text()
declarations = set()
for module, expected in modules.items():
    source = root / f"lean/MicroCFTA/{module}.lean"
    assert digest(source) == expected, source
    assert digest(evidence / f"{module}.lean") == expected, module
    for declaration in re.findall(r"^(?:theorem|def|structure|inductive|abbrev) ([A-Za-z_][A-Za-z_0-9.]*)", source.read_text(), re.M):
        name = f"MicroCFTA.{module}.{declaration}"
        assert f"#print axioms {name}\n" in public_text, name
        assert f"#check @{name}\n" in public_text, name
        declarations.add(name)
assert len(declarations) == 50

kernel_logs = {
    "state-kernels.lean": "state-kernels-1.log",
    "actual-kernels.lean": "actual-kernels-3.log",
    "initial-independent-review-kernels.lean": "initial-independent-review-kernels-1.log",
    "root-kernels.lean": "root-kernels-2.log",
    "edge-call-kernels.lean": "edge-call-kernels-6.log",
    "entries-kernels.lean": "entries-kernels-1.log",
    "recursion-kernels.lean": "recursion-kernels-1.log",
    "rows-kernels.lean": "rows-kernels-1.log",
    "node-kernels.lean": "node-kernels-2.log",
    "node-root-independent-kernels.lean": "node-root-independent-kernels-2.log",
}
extra_public_logs = [
    "state-public-1.log", "actual-public-1.log", "edge-call-checks-1.log",
    "entries-public-1.log", "recursion-public-1.log", "rows-checks-1.log",
    "construction-initial-public-2.log",
]
allowed = {"propext", "Classical.choice", "Quot.sound"}
final_logs = ["all-public-1.log", *extra_public_logs, *kernel_logs.values()]
for name in final_logs:
    text = (evidence / name).read_text()
    assert not re.search(r"error:|warning:|sorryAx", text), name
    for found in re.findall(r"depends on axioms: \[(.*?)\]", text, re.S):
        assert {axiom.strip().split(".{", 1)[0] for axiom in found.split(",")} <= allowed, (name, found)

kernel_count = 0
for source, log in kernel_logs.items():
    text = (evidence / source).read_text()
    printed = re.findall(r"^#print axioms (\S+)", text, re.M)
    checked = re.findall(r"^#check @(\S+)", text, re.M)
    assert printed == checked and printed, source
    kernel_count += len(printed)
    assert all(name in (evidence / log).read_text() for name in printed), log
assert kernel_count == 24, kernel_count

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

audit = (evidence / "audit-2.log").read_text()
assert "Build completed successfully (2531 jobs)." in audit
assert "Checked axiom dependencies of 59275 MicroCFTA theorems." in audit
report = {
    "result": "PASS", "frozen_modules": len(modules),
    "declared_public_pairs": len(declarations), "integration_pairs": kernel_count,
    "allowed_axioms": sorted(allowed), "audit_jobs": 2531,
    "audit_dependency_checks": 59275, "audit_log_sha256": digest(evidence / "audit-2.log"),
    "final_probe_logs": {name: digest(evidence / name) for name in final_logs},
    "checked_component_manifest_entries": manifest_entries, "component_manifests": manifests,
    "completion_boundary": "One finite ordinary pass, conditional on independently reached parent entry ranges.",
    "remaining": "Quantitative capacity, general Mu/union/reference progress, repeated passes, frontends, concrete runtime, and full pipeline.",
}
(evidence / "checkpoint-validation.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
