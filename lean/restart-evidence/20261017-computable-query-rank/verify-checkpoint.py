"""Verify initial instruction credit and complete checked query resource budgets."""

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


expected_totals = json.loads((evidence / "expected-validation.json").read_text())
modules = json.loads((evidence / "frozen-modules.json").read_text())
assert len(modules) == expected_totals["production_modules"]
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
    for setting in ["pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.universes true", "pp.deepTerms true"]:
        assert f"set_option {setting}" in source, (label, setting)
    max_steps = re.search(r"set_option pp.maxSteps (\d+)", source)
    assert max_steps and int(max_steps.group(1)) >= 1000000, label
    results[label] = {"pairs": spec["pairs"], "axioms": sorted(observed), "source_sha256": digest(evidence / spec["source"]), "log_sha256": digest(evidence / spec["log"])}

builds = {}
for name in json.loads((evidence / "build-logs.json").read_text()):
    log = (evidence / name).read_text()
    assert "Build completed successfully" in log, name
    assert not re.search(r"error:|sorryAx|depends on forbidden axiom", log), name
    builds[name] = {"sha256": digest(evidence / name), "jobs": int(re.search(r"Build completed successfully \((\d+) jobs\)", log).group(1))}
    if name.startswith("lean-audit"):
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

assert len(used_resolutions) == len(resolutions)
strict = json.loads((evidence / "current-strict-logs.json").read_text())
assert set(strict) == set(modules)
for name, spec in strict.items():
    assert spec["exit_code"] == 0 and (evidence / spec["log"]).stat().st_size == 0, name
    assert spec["source_sha256"] == modules[name], name
assert len(results) == expected_totals["probe_groups"] and sum(item["pairs"] for item in results.values()) == expected_totals["probe_pairs"]
assert len(manifests) == expected_totals["component_manifests"] and sum(item["entries"] for item in manifests.values()) == expected_totals["component_manifest_entries"]
report = {"historical_input_snapshots": used_resolutions, "modules": modules, "probes": results, "total_pairs": sum(item["pairs"] for item in results.values()), "builds": builds, "component_manifests": manifests, "component_manifest_entries": sum(item["entries"] for item in manifests.values()), "scope": "Full recursive source mass and literal input inventory give a computable natural semantic rank. Stable execution is constructed without a supplied completed query. Numeric source counters and causal mass bound branching and instruction credit. Closed original roots, physical semantic readiness, idle warm tables, causal Stored, and initial numeric headroom construct their own checked receipt and bound that same trace, exact execute, result, store, and identity supplies by the computed schedule. No future trace, WordRanges, instruction count, later counter, or desired result law is an initial premise. General result-fed serial query composition, constrained execution, convergence, concrete capacity, current adapters, and complete public Haskell correspondence remain open."}
print(json.dumps(report, indent=2))
