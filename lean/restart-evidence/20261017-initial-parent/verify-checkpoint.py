"""Verify initial parent construction and outer edge memo completion evidence."""

import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent

subprocess.run(["python3", str(HERE / "prepare-evidence.py")], cwd=ROOT, check=True, capture_output=True, text=True)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(name: str):
    return json.loads((HERE / name).read_text())


modules = load("frozen-modules.json")
assert list(modules) == load("new-modules.json")
expected = load("expected-validation.json")
assert len(modules) == expected["production_modules"]
handwritten = set()
fields = set()
for module, sha in modules.items():
    path = ROOT / "lean/MicroCFTA" / f"{module}.lean"
    assert digest(path) == sha, module
    source = path.read_text()
    assert not re.search(r"\b(sorry|axiom|unsafe)\b|set_option linter\.[^\n]*false", source)
    handwritten.update(
        f"MicroCFTA.{module}.{name}" for name in re.findall(
            r"^(?:(?:noncomputable )?def|abbrev|structure|inductive|theorem) ([\w.]+)", source, re.M
        )
    )
    if "structure Receipt " in source:
        receipt = source.split("structure Receipt ", 1)[1].split("\n/--", 1)[0]
        fields.update(f"MicroCFTA.{module}.Receipt.{name}" for name in re.findall(r"^  (\w+) :", receipt, re.M))
public = handwritten | fields
assert len(handwritten) == expected["handwritten_public_declarations"]
assert len(fields) == expected["additional_checked_public_fields"]
assert len(public) == expected["distinct_public_declarations"]

strict = load("current-strict-logs.json")
assert set(strict) == set(modules)
for module, item in strict.items():
    assert item["exit_code"] == 0
    assert (HERE / item["log"]).read_bytes() == b""
    assert digest(HERE / item["source"]) == modules[module]
    assert item["source_sha256"] == modules[module]

builds = {}
for name in load("build-logs.json"):
    log = (HERE / name).read_text()
    assert not re.search(r"error:|sorryAx|depends on forbidden axiom|warning: MicroCFTA/SourceCurrent", log), name
    jobs = re.search(r"Build completed successfully \((\d+) jobs\)", log)
    assert jobs, name
    builds[name] = {"sha256": digest(HERE / name), "jobs": int(jobs.group(1))}
    if name == "lean-audit.log":
        assert log.startswith("4294967296\n4294967296\n0\n")
        builds[name]["dependency_checks"] = int(re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", log).group(1))
assert len(builds) == len(modules) + 1
audit = load("audit-execution.json")
assert audit["exit_code"] == 0
assert audit["effective_memory_max_bytes"] == audit["effective_memory_high_bytes"] == 4294967296
assert audit["effective_memory_swap_max_bytes"] == 0
assert audit["peak_mib"] == 361
assert (HERE / "lean-audit-attempt-1.log").read_text() == "Failed to connect to bus: No medium found\n"

allowed = {"propext", "Classical.choice", "Quot.sound"}
probes = {}
checked_public = set()
for label, spec in load("kernel-logs.json").items():
    source = (HERE / spec["source"]).read_text()
    log = (HERE / spec["log"]).read_text()
    assert spec["exit_code"] == 0
    assert not re.search(r"error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|…|\.\.\.", log), label
    checks = re.findall(r"^#check @(\S+)", source, re.M)
    axioms = re.findall(r"^#print axioms (\S+)", source, re.M)
    assert checks == axioms and len(checks) == spec["pairs"] == len(set(checks)), label
    for setting in ["linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.universes true", "pp.deepTerms true"]:
        assert f"set_option {setting}" in source, (label, setting)
    assert re.search(r"set_option pp.maxSteps (\d+)", source)
    assert int(re.search(r"set_option pp.maxSteps (\d+)", source).group(1)) >= 1000000
    if label.endswith("public"):
        checked_public.update(checks)
        assert re.findall(r"^#print (?!axioms )(\S+)", source, re.M) == checks
        assert "set_option pp.proofs.threshold 254" in source
    blocks = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", log, re.S)
    assert len(blocks) + log.count("does not depend on any axioms") == len(checks), label
    observed = set()
    for block in blocks:
        observed.update(re.sub(r"\.\{[^}]+\}", "", name.strip()) for name in block.split(",") if name.strip())
    assert observed <= allowed, (label, observed)
    assert all(name in log for name in checks), label
    probes[label] = {"pairs": len(checks), "axioms": sorted(observed), "source_sha256": digest(HERE / spec["source"]), "log_sha256": digest(HERE / spec["log"])}
assert checked_public == public
assert len(probes) == expected["probe_groups"]
assert sum(item["pairs"] for item in probes.values()) == expected["probe_pairs"]
assert sum(item["pairs"] for label, item in probes.items() if not label.endswith("public")) == expected["constructed_integration_declarations"]
assert sum(item["pairs"] for label, item in probes.items() if label.endswith("public")) == len(public)


def references(value):
    if isinstance(value, dict):
        if "path" in value and "sha256" in value:
            yield value["path"], value["sha256"]
        else:
            for child in value.values():
                yield from references(child)
    elif isinstance(value, list):
        for child in value:
            yield from references(child)


manifests = {}
for path in sorted(HERE.glob("*-manifest.json")):
    data = json.loads(path.read_text())
    entries = list(references(data["entries"]))
    refs = list(references(data))
    assert entries and len(entries) == len({name for name, _ in entries}), path
    for name, sha in refs:
        assert digest(ROOT / name) == sha, (path, name)
    manifests[path.name] = {"entries": len(entries), "hash_references": len(refs), "sha256": digest(path)}
assert len(manifests) == expected["component_manifests"]
assert sum(item["entries"] for item in manifests.values()) == expected["component_manifest_entries"]
assert sum(item["hash_references"] for item in manifests.values()) == expected["component_hash_references"]
for verifier in load("component-verifiers.json"):
    subprocess.run(["python3", str(HERE / verifier)], cwd=ROOT, check=True, capture_output=True, text=True)

print(json.dumps({
    "modules": modules,
    "handwritten_public_declarations": len(handwritten),
    "additional_checked_public_fields": len(fields),
    "distinct_public_declarations": len(public),
    "probes": probes,
    "total_pairs": sum(item["pairs"] for item in probes.values()),
    "builds": builds,
    "component_manifests": manifests,
    "component_manifest_entries": sum(item["entries"] for item in manifests.values()),
    "component_hash_references": sum(item["hash_references"] for item in manifests.values()),
    "scope": load("scope.json"),
}, indent=2))
