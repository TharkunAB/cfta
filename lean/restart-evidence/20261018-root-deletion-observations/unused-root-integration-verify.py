import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LIMITS = {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((HERE / "unused-root-integration-manifest.json").read_text())
    for entry in manifest["entries"]:
        path = ROOT / entry["path"]
        assert path.stat().st_size == entry["bytes"], path
        assert sha(path) == entry["sha256"], path
    selected = json.loads((HERE / "unused-root-integration-selection.json").read_text())
    assert selected["finalized"] and selected["owned_lean_runs"] == 2
    assert [selected[k] for k in ["public_pairs", "constructed_pairs", "auxiliary_pairs"]] == [0, 1, 0]
    assert selected["canonical"] is None and not selected["retained_unselected"]
    assert sha(ROOT / selected["production_dependency"]) == selected["production_dependency_sha256"]
    strict = json.loads((HERE / (selected["strict"] + ".json")).read_text())
    assert strict["sha256"] == selected["source_sha256"] == sha(HERE / selected["source"])
    assert (HERE / strict["source"]).read_bytes() == (HERE / selected["source"]).read_bytes()
    assert not (HERE / strict["log"]).read_bytes()
    for stem in [selected["strict"]] + [g["name"] for g in selected["groups"]]:
        receipt = json.loads((HERE / (stem + ".json")).read_text())
        assert receipt["exit_code"] == 0
        assert receipt["wrapper"][:5] == ["/home/tritlo/Code/heavy-management/bin/capped", "--mem", "4G", "--time", "5m"]
        assert json.loads((HERE / receipt["limits"]).read_text()) == LIMITS
        assert sha(HERE / receipt["source"]) == receipt["sha256"]
    spec = importlib.util.spec_from_file_location("unused_root_integration_probes", HERE / "unused-root-integration-probe-check.py")
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    for group in selected["groups"]:
        probes.check_group(group)
    source = (HERE / selected["source"]).read_text()
    assert source.count("\ntheorem ") == 1
    private = source.split("private theorem checked ", 1)[1].split(" := by\n", 1)[0]
    public = source.split("theorem actual_unused ", 1)[1].split(" := checked kind warm", 1)[0]
    assert private == public
    assert "SourceCurrentNativeUnusedRootDeletion.build" in source
    assert "current_history kind warm" in source
    assert "reduced (unused kind warm)" in source
    assert "Ready" not in public and "Correct" not in public
    assert manifest["groups"] == selected["groups"]
    print(json.dumps({"status": "PASS", "entries": len(manifest["entries"]),
        "public_pairs": 0, "constructed_pairs": 1, "auxiliary_pairs": 0,
        "owned_lean_runs": 2, "source_cases": 4, "entry_modes": 2,
        "scope": "actual cold/warm unused source reduction with derived histories and arbitrary root cuts/profile assignments"}, sort_keys=True))


if __name__ == "__main__":
    main()
