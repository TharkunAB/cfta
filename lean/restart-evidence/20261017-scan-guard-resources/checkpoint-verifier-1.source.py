"""Verify initial complete Scans, guard schedules, and retained caller state."""

import gzip
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
    source = without_comments(path.read_text())
    assert not re.search(r"\b(sorry|axiom)\b|(?:\bby\s+|^\s*)admit(?:\s|$)", source, re.M), name

public_names = set()
for module in modules:
    source = (root / "lean/MicroCFTA" / f"{module}.lean").read_text()
    namespace = module
    public_names |= {f"MicroCFTA.{namespace}.{name}" for name in re.findall(r"^(?:(?:noncomputable )?def|abbrev|structure|inductive|theorem) ([\w.]+)", source, re.M)}
handwritten_public = set(public_names)
receipt_source = (root / "lean/MicroCFTA/SourceCurrentScanNumeric.lean").read_text()
receipt_fields = re.findall(r"^  ([a-zA-Z]\w*) :", receipt_source, re.M)
assert len(receipt_fields) == 10
public_names |= {f"MicroCFTA.SourceCurrentScanNumeric.Receipt.{name}" for name in receipt_fields}
assert len(handwritten_public) == expected_totals["handwritten_public_declarations"]
assert len(public_names) - len(handwritten_public) == expected_totals["additional_checked_public_fields"]
checked_public = set()
for label, spec in json.loads((evidence / "kernel-logs.json").read_text()).items():
    if label.endswith("public"):
        checked_public |= set(re.findall(r"^#check @(\S+)", (evidence / spec["source"]).read_text(), re.M))
assert public_names == checked_public
assert len(public_names) == expected_totals["distinct_public_declarations"]

allowed = {"propext", "Classical.choice", "Quot.sound"}
probes = json.loads((evidence / "kernel-logs.json").read_text())
results = {}
for label, spec in probes.items():
    source = (evidence / spec["source"]).read_text()
    log_path = evidence / spec["log"]
    log = gzip.decompress(log_path.read_bytes()).decode() if log_path.suffix == ".gz" else log_path.read_text()
    assert not re.search(r"error(?:\(|:)|warning(?:\(|:)|sorryAx|truncated|⋯|\.\.\.", log), label
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
    assert not re.search(r"error:|sorryAx|depends on forbidden axiom|warning: MicroCFTA/SourceCurrent", log), name
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
    entries = list(manifest_entries(data["entries"]))
    references = list(manifest_entries(data))
    assert entries, path
    if "entry_count" in data:
        assert len(entries) == data["entry_count"], path
    for name, expected in references:
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
    manifests[path.name] = {"entries": len(entries), "hash_references": len(references), "sha256": digest(path)}

assert len(used_resolutions) == len(resolutions)
strict = json.loads((evidence / "current-strict-logs.json").read_text())
assert set(strict) == set(modules)
for name, spec in strict.items():
    assert spec["exit_code"] == 0 and (evidence / spec["log"]).stat().st_size == 0, name
    assert spec["source_sha256"] == modules[name], name
    assert digest(evidence / spec["source"]) == modules[name], name
assert len(results) == expected_totals["probe_groups"] and sum(item["pairs"] for item in results.values()) == expected_totals["probe_pairs"]
public_pairs = sum(item["pairs"] for label, item in results.items() if label.endswith("public"))
assert public_pairs - len(public_names) == expected_totals["repeated_public_pairs"]
assert sum(item["pairs"] for label, item in results.items() if not label.endswith("public")) == expected_totals["constructed_integration_declarations"]
assert len(manifests) == expected_totals["component_manifests"] and sum(item["entries"] for item in manifests.values()) == expected_totals["component_manifest_entries"]
assert sum(item["hash_references"] for item in manifests.values()) == expected_totals["component_hash_references"]
report = {"historical_input_snapshots": used_resolutions, "modules": modules, "distinct_public_declarations": len(public_names), "handwritten_public_declarations": len(handwritten_public), "additional_checked_public_fields": len(receipt_fields), "probes": results, "total_pairs": sum(item["pairs"] for item in results.values()), "builds": builds, "component_manifests": manifests, "component_manifest_entries": sum(item["entries"] for item in manifests.values()), "component_hash_references": sum(item["hash_references"] for item in manifests.values()), "scope": "Initial finite guard alphabets advance through every actual checked native instruction. Pure initial class schedules construct full current Scans at actual returned heaps, derive the older reached range interfaces, and retain full Frame, numeric Fits, finite guard carrier, effects, original values, fourth-memo validity and Extends, and the same worker result at every independently larger choice of five fuels. The caller constructs strict logical source reads, complete same-inventory Post, exact outer tables and Merge, original selected order and multiplicity, and sound stopped-class refutation. Initial assumptions remain Frame, Fits, valid memos, proper paths, active classes for refutation, and pure initial query reservations. No future graph, reached ranges, worker success, finite input Cap or whole-forest closedness is a producer premise. AnswerSound remains one-sided. These are logical, partly noncomputable bounds, not extracted Haskell budgets or host capacity. Remaining Required cap support, complete source control flow and outer descent, arbitrary recursive callers, convergence, current adapters, lazy Haskell forcing, runtime and whole public Haskell correspondence remain open."}
print(json.dumps(report, indent=2))
