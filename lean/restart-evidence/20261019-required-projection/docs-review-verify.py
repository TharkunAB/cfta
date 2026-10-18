"""Verify the reviewed document bytes and reused frozen proof evidence."""

from pathlib import Path
import hashlib
import json
import re


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
OPTIONS = [
    "linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true",
    "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true",
    "pp.maxSteps 10000000",
]
LIMITS = {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
BAD = r"sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|maximum recursion depth|maximum number of heartbeats|pp\.rawOnError|⋯|…|\.\.\."


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_files(manifest):
    for item in manifest["files"]:
        path = ROOT / item["path"]
        assert path.stat().st_size == item["bytes"], item["path"]
        assert sha(path) == item["sha256"], item["path"]


def metadata(directory, stem):
    data = json.loads((directory / (stem + ".json")).read_text())
    assert data["exit_code"] == 0, stem
    assert data["wrapper"][1:5] == ["--mem", "4G", "--time", "5m"], stem
    assert json.loads((directory / data["limits"]).read_text()) == LIMITS, stem
    if "source" in data:
        assert sha(directory / data["source"]) == data["sha256"], stem
    return data


def group(item):
    data = metadata(HERE, item["name"])
    source = (HERE / data["source"]).read_text()
    log = (HERE / data["log"]).read_text()
    for option in OPTIONS:
        assert "set_option " + option in source, (item["name"], option)
    for pattern in [r"^#check @", r"^#print (?!axioms )", r"^#print axioms "]:
        assert len(re.findall(pattern, source, re.M)) == item["pairs"], item["name"]
    assert not re.search(BAD, log), item["name"]
    reports = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", log)
    assert len(reports) + log.count("does not depend on any axioms") == item["pairs"]
    for report in reports:
        cleaned = re.sub(r"\.\{[^}]*\}", "", report)
        assert set(re.split(r",\s*", cleaned.strip())) <= {"propext", "Classical.choice", "Quot.sound"}


def main():
    manifest = json.loads((HERE / "docs-review-manifest.json").read_text())
    check_files(manifest)
    totals = {"new-public": 0, "constructed": 0}
    stricts = []
    groups = []
    for prefix in ["required-projection", "required-target", "class-structural"]:
        component = json.loads((HERE / (prefix + "-manifest.json")).read_text())
        check_files(component)
        selection = json.loads((HERE / (prefix + "-selection.json")).read_text())
        assert selection["finalized"]
        direct = metadata(HERE, selection["strict"])
        assert direct["sha256"] == selection["sha256"] == sha(ROOT / selection["production"])
        stricts.append(selection["strict"])
        for item in selection["groups"]:
            totals[item["kind"]] += item["pairs"]
            groups.append(item)
        if "fixture_strict" in selection:
            stricts.append(selection["fixture_strict"])
    assert totals == {"new-public": 6, "constructed": 1}
    assert len(stricts) == len(groups) == 4
    for stem in stricts:
        data = metadata(HERE, stem)
        assert (HERE / data["log"]).read_bytes() == b"", stem
    for item in groups:
        group(item)
    current = metadata(HERE, "full-audit-1")
    assert current["command"][-1] == "build"
    log = (HERE / current["log"]).read_text()
    assert "Build completed successfully (3440 jobs)." in log
    assert "Checked axiom dependencies of 73626 MicroCFTA theorems." in log
    assert len(re.findall(r"^warning:", log, re.M)) == 1
    assert "InternedFreshOrdinaryClosedCompletion.lean:24:5" in log
    previous = HERE.parent / "20261019-mu-source-handoff"
    old = json.loads((previous / "full-audit-1.json").read_text())
    assert old["exit_code"] == 0 and old["command"][-2:] == ["build", "MicroCFTA.Audit"]
    old_log = (previous / old["log"]).read_text()
    assert "Build completed successfully (3435 jobs)." in old_log
    assert "Checked axiom dependencies of 73598 MicroCFTA theorems." in old_log
    blocks = []
    for name in manifest["authority_documents"]:
        text = (ROOT / name).read_text()
        start = text.index("## Current Required projection and structural class sources")
        end = text.index("## Current open native and Required source handoffs", start)
        blocks.append(text[start:end])
    assert len(blocks) == 7 and len(set(blocks)) == 1
    assert "Any recursive Merge Run uses the prepared children." in re.sub(r"\s+", " ", blocks[0])
    assert (ROOT / "FINDINGS.md").read_text().splitlines()[2] == "## Haskell fix handoff for external work"
    print(json.dumps({
        "status": "PASS", "manifest_pins": len(manifest["files"]),
        "owned_lean_runs": 0, "owned_public_pairs": 0, "owned_constructed_pairs": 0,
        "reused_public_pairs": 6, "reused_constructed_pairs": 1,
        "reused_strict_zero_logs": 4, "reused_full_groups": 4,
        "identical_authority_blocks": 7, "reviewed_documents": 10,
        "current_build": "lake build: 3440 jobs / 73626 Audit dependencies",
        "previous_build": "lake build MicroCFTA.Audit: 3435 jobs / 73598 dependencies",
    }))


if __name__ == "__main__":
    main()
