"""Check current proof source hashes, public probes, and component evidence."""

import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

modules = json.loads((evidence / "frozen-modules.json").read_text())
public_sources = {
    "merge-cache-public.lean": "merge-cache-public-1.log",
    "merge-cache-definition-public.lean": "merge-cache-definition-public-1.log",
    "merge-code-public.lean": "merge-code-public-1.log",
    "merge-public.lean": "merge-public-1.log",
    "merge-worker-public.lean": "merge-worker-public-1.log",
    "projection-checks.lean": "projection-checks-4.log",
    "required-public.lean": "required-public-1.log",
    "target-checks.lean": "target-checks-4.log",
    "shared-public.lean": "shared-public-1.log",
}
kernel_sources = {
    "merge-cache-kernels.lean": "merge-cache-kernels-2.log",
    "merge-kernels.lean": "merge-kernels-2.log",
    "merge-worker-kernels.lean": "merge-worker-kernels-1.log",
    "projection-checks.lean": "projection-checks-4.log",
    "required-kernels.lean": "required-kernels-3.log",
    "target-checks.lean": "target-checks-4.log",
    "shared-kernels.lean": "shared-kernels-2.log",
}
public_text = "\n".join((evidence / name).read_text() for name in public_sources)
public_count = 0
public_declarations = set()
for module, expected in modules.items():
    path = root / f"lean/MicroCFTA/{module}.lean"
    assert digest(path) == expected, path
    declarations = re.findall(r"^(?:theorem|def|structure|inductive|abbrev) ([A-Za-z_][A-Za-z_0-9]*)", path.read_text(), re.M)
    for declaration in declarations:
        name = f"MicroCFTA.{module}.{declaration}"
        assert f"#print axioms {name}\n" in public_text, name
        assert f"#check @{name}\n" in public_text, name
        public_count += 1
        public_declarations.add(name)

allowed = {"propext", "Classical.choice", "Quot.sound"}
final_logs = sorted(set(public_sources.values()) | set(kernel_sources.values()))
for name in final_logs:
    text = (evidence / name).read_text()
    assert not re.search(r"error:|warning:|sorryAx", text), name
    for found in re.findall(r"depends on axioms: \[(.*?)\]", text, re.S):
        assert {axiom.strip().split(".{", 1)[0] for axiom in found.split(",")} <= allowed, (name, found)

kernel_count = 0
for name in kernel_sources:
    text = (evidence / name).read_text()
    printed = re.findall(r"^#print axioms (\S+)", text, re.M)
    checked = re.findall(r"^#check @(\S+)", text, re.M)
    assert printed == checked, name
    kernel_count += sum(name not in public_declarations for name in printed)

manifest_entries = 0
manifest_hashes = {}
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
for path in sorted(evidence.glob("*-manifest.json")):
    check_entries(json.loads(path.read_text()))
    manifest_hashes[path.name] = digest(path)

audit = (evidence / "audit-1.log").read_text()
assert "Build completed successfully (2508 jobs)." in audit
assert "Checked axiom dependencies of 59107 MicroCFTA theorems." in audit
report = {
    "result": "PASS", "frozen_modules": len(modules), "public_declaration_pairs": public_count,
    "integration_pairs": kernel_count, "allowed_axioms": sorted(allowed),
    "checked_component_manifest_entries": manifest_entries, "component_manifests": manifest_hashes,
    "final_probe_logs": {name: digest(evidence / name) for name in final_logs},
    "audit_jobs": 2508, "audit_dependency_checks": 59107, "audit_log_sha256": digest(evidence / "audit-1.log"),
}
(evidence / "checkpoint-validation.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
