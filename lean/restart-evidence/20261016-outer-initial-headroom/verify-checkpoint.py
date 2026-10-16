"""Verify frozen initial outer resources and passing kernel probes."""

import hashlib
import json
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def without_comments(source: str) -> str:
    result = []
    index = 0
    depth = 0
    while index < len(source):
        pair = source[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
                result.append(" ")
            else:
                index += 1
        elif pair == "/-":
            depth = 1
            index += 2
        elif pair == "--":
            newline = source.find("\n", index)
            index = len(source) if newline == -1 else newline
        else:
            result.append(source[index])
            index += 1
    assert depth == 0
    return "".join(result)


modules = json.loads((evidence / "frozen-modules.json").read_text())
for name, expected in modules.items():
    path = root / "lean/MicroCFTA" / f"{name}.lean"
    assert digest(path) == expected, name
    assert not re.search(r"\b(sorry|admit|axiom)\b", without_comments(path.read_text())), name

allowed = {"propext", "Classical.choice", "Quot.sound"}
probes = json.loads((evidence / "kernel-logs.json").read_text())
results = {}
for label, spec in probes.items():
    source = (evidence / spec["source"]).read_text()
    log = (evidence / spec["log"]).read_text()
    assert not re.search(r"error:|warning:|sorryAx|truncated|⋯|\.\.\.", log), label
    declarations = re.findall(r"^#print axioms (\S+)", source, re.M)
    assert len(declarations) == spec["pairs"], label
    assert len(re.findall(r"^#check @", source, re.M)) == spec["pairs"], label
    observed = set()
    blocks = re.findall(r"depends on axioms: \[([^\]]*)\]", log, re.S)
    no_axioms = re.findall(r"does not depend on any axioms", log)
    assert len(blocks) + len(no_axioms) == spec["pairs"], label
    for block in blocks:
        observed |= {re.sub(r"\.\{[^}]+\}", "", name.strip()) for name in block.split(",") if name.strip()}
    assert observed <= allowed, (label, observed)
    for name in declarations:
        assert name in log, (label, name)
    for setting in ["pp.explicit true", "pp.proofs true", "pp.universes true", "pp.deepTerms true"]:
        assert f"set_option {setting}" in source, (label, setting)
    max_steps = re.search(r"set_option pp.maxSteps (\d+)", source)
    assert max_steps and int(max_steps.group(1)) >= 1000000, label
    results[label] = {"pairs": spec["pairs"], "axioms": sorted(observed), "source_sha256": digest(evidence / spec["source"]), "log_sha256": digest(evidence / spec["log"])}

builds = {}
for name in ['uniform-native-work-build-1.log', 'outer-budget-numbers-build-1.log', 'actual-target-work-build-1.log', 'shared-uniform-capacity-build-1.log', 'actual-edit-canonical-1.log', 'actual-classpass-canonical-1.log', 'actual-parent-canonical-1.log', 'resource-children-canonical-3.log', 'resource-root-canonical-1.log', 'resource-root-prepared-canonical-2.log', 'lean-audit.log']:
    log = (evidence / name).read_text()
    assert "Build completed successfully" in log, name
    assert not re.search(r"error:|sorryAx|depends on forbidden axiom", log), name
    builds[name] = {"sha256": digest(evidence / name), "jobs": int(re.search(r"Build completed successfully \((\d+) jobs\)", log).group(1))}
    if name == "lean-audit.log":
        builds[name]["dependency_checks"] = int(re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", log).group(1))

def manifest_entries(value):
    if isinstance(value, dict):
        if "path" in value and "sha256" in value:
            yield value["path"], value["sha256"]
        elif value and all(isinstance(key, str) and "/" in key and isinstance(expected, str) and re.fullmatch(r"[0-9a-f]{64}", expected) for key, expected in value.items()):
            yield from value.items()
        else:
            for child in value.values():
                yield from manifest_entries(child)
    elif isinstance(value, list):
        for child in value:
            yield from manifest_entries(child)


resolutions = json.loads((evidence / "historical-snapshots.json").read_text())
resolution_map = {(item["manifest"], item["path"], item["sha256"]): item for item in resolutions}
used_resolutions = []
manifests = {}
for path in sorted(set(evidence.glob("*-manifest.json")) | set(evidence.glob("*-reviewed-hashes.json"))):
    data = json.loads(path.read_text())
    entries = list(manifest_entries(data))
    assert entries, path
    for name, expected in entries:
        if digest(root / name) != expected:
            key = (path.name, name, expected)
            assert key in resolution_map, (path, name)
            item = resolution_map[key]
            if "snapshot" in item:
                original = (root / item["snapshot"]).read_bytes()
            else:
                original = subprocess.run(["git", "show", item["git_object"]], cwd=root, check=True, capture_output=True).stdout
            assert hashlib.sha256(original).hexdigest() == expected, item
            used_resolutions.append(item)
    manifests[path.name] = {"entries": len(entries), "sha256": digest(path)}

assert len(used_resolutions) == len(resolutions) == 0
report = {"historical_input_snapshots": used_resolutions, "modules": modules, "probes": results, "total_pairs": sum(item["pairs"] for item in results.values()), "builds": builds, "component_manifests": manifests, "component_manifest_entries": sum(item["entries"] for item in manifests.values()), "scope": "Initial uniform parent capacity, actual constructor Work through all eight outer families, and constructed/prepared finite ordinary root execution from initial computed profiles and headroom. No reached-entry Plan input. The old universal raw Reach NumericPlan bridge, general recursion, convergence, frontend/runtime correspondence, and full-library composition remain open."}
(evidence / "checkpoint-validation.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
