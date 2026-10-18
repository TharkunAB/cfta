"""Check the frozen review files and the reused selected receipts."""

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
LIMITS = {
    "memory.max": "4294967296", "memory.high": "4294967296",
    "memory.swap.max": "0",
}
BAD = (
    r"sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|"
    r"maximum recursion depth|maximum number of heartbeats|pp\.rawOnError|⋯|…|\.\.\."
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def metadata(stem):
    data = json.loads((HERE / (stem + ".json")).read_text())
    assert data["exit_code"] == 0, stem
    assert data["wrapper"][1:5] == ["--mem", "4G", "--time", "5m"], stem
    assert "leanprover--lean4---v4.34.1/bin/" in data["command"][0], stem
    assert json.loads((HERE / data["limits"]).read_text()) == LIMITS, stem
    if "source" in data:
        assert sha(HERE / data["source"]) == data["sha256"], stem
    return data


def check_group(item):
    stem = item["name"]
    data = metadata(stem)
    source = (HERE / data["source"]).read_text()
    log = (HERE / data["log"]).read_text()
    for option in OPTIONS:
        assert "set_option " + option in source, (stem, option)
    assert re.findall(r"^#check @(.+)$", source, re.M) == [item["head"]], stem
    assert re.findall(r"^#print (?!axioms )(.+)$", source, re.M) == [item["head"]], stem
    assert re.findall(r"^#print axioms (.+)$", source, re.M) == [item["head"]], stem
    assert not re.search(BAD, log), stem
    reports = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", log)
    assert len(reports) == 1, stem
    axioms = re.sub(r"\.\{[^}]*\}", "", reports[0])
    assert set(re.split(r",\s*", axioms.strip())) <= {
        "propext", "Classical.choice", "Quot.sound",
    }, stem
    assert item["head"] in log, stem


def check_alias(fixture):
    old = (ROOT / fixture["comparison_source"]).read_text()
    new = (ROOT / fixture["path"]).read_text()
    old_token = "theorem actual_changed_children :"
    old_start = old.index(old_token)
    old_type = old[old_start + len(old_token):old.index(" :=", old_start)]
    for token in ["private theorem checked_witness :", old_token]:
        start = new.index(token)
        assert new[start + len(token):new.index(" :=", start)] == old_type
    old_proof = old[
        old.index(" := by", old_start) + len(" := by"):old.index("\n\nend", old_start)
    ].strip()
    start = new.index("private theorem checked_witness :")
    new_proof = new[
        new.index(" := by", start) + len(" := by"):new.index("/-- A source-built", start)
    ].strip()
    assert old_proof == new_proof


def main():
    manifest = json.loads((HERE / "final-required-review-manifest.json").read_text())
    for item in manifest["files"]:
        path = ROOT / item["path"]
        assert path.stat().st_size == item["bytes"], item["path"]
        assert sha(path) == item["sha256"], item["path"]
    selection = json.loads((HERE / "final-required-review-selection.json").read_text())
    assert selection["status"] == "final"
    for item in selection["production"]:
        data = metadata(item["strict"])
        assert (HERE / data["log"]).read_bytes() == b"", item["strict"]
        assert sha(ROOT / item["path"]) == item["sha256"]
        assert data["sha256"] == item["sha256"]
        canonical = metadata(item["canonical"])
        log = (HERE / canonical["log"]).read_text()
        assert "Build completed successfully" in log
        assert len(re.findall(r"^warning:", log, re.M)) == 1
        assert "InternedFreshOrdinaryClosedCompletion.lean:24:5" in log
        assert not re.search(r"\berror:", log)
    fixture = selection["fixture"]
    data = metadata(fixture["strict"])
    assert (HERE / data["log"]).read_bytes() == b""
    assert sha(ROOT / fixture["path"]) == fixture["sha256"]
    assert data["sha256"] == fixture["sha256"]
    check_alias(fixture)
    for item in selection["reused_groups"]:
        check_group(item)
    print(json.dumps({
        "status": "PASS", "manifest_pins": len(manifest["files"]),
        "owned_lean_runs": 0, "owned_public_pairs": 0,
        "owned_constructed_pairs": 0, "reused_public_pairs": 2,
        "reused_constructed_pairs": 1, "reused_strict_zero_logs": 3,
        "fixture_statements_and_renamed_proof_identical": True,
        "canonical": "Both pass with one unchanged dependency warning each",
    }))


if __name__ == "__main__":
    main()
