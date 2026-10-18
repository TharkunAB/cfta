import hashlib
import importlib.util
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LIMITS = {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((HERE / "deletion-filter-manifest.json").read_text())
    for entry in manifest["entries"]:
        path = ROOT / entry["path"]
        assert path.stat().st_size == entry["bytes"], path
        assert sha(path) == entry["sha256"], path
    selected = json.loads((HERE / "deletion-filter-selection.json").read_text())
    assert selected["finalized"]
    assert [selected[k] for k in ["public_pairs", "constructed_pairs", "auxiliary_pairs"]] == [2, 3, 0]
    production = ROOT / selected["production"]
    assert sha(production) == selected["sha256"]
    meta = json.loads((HERE / (selected["strict"] + ".json")).read_text())
    assert meta["sha256"] == selected["sha256"]
    assert (HERE / meta["source"]).read_bytes() == production.read_bytes()
    assert sha(ROOT / "lean/MicroCFTA/SourceCurrentStoredMuRootContract.lean") == selected["root_contract_final_sha256"]
    assert sha(HERE / selected["root_contract_used_source"]) == selected["root_contract_used_sha256"]
    stems = [selected["strict"], selected["canonical"]] + selected["constructed_strict"]
    stems += [g["name"] for g in selected["groups"]]
    expected = {stem: 0 for stem in stems}
    expected.update({item["stem"]: item["exit_code"] for item in selected["retained_unselected"]})
    assert len(expected) == selected["owned_lean_runs"] == 16
    for stem, code in expected.items():
        receipt = json.loads((HERE / (stem + ".json")).read_text())
        assert receipt["exit_code"] == code, stem
        assert receipt["wrapper"][:5] == ["/home/tritlo/Code/heavy-management/bin/capped", "--mem", "4G", "--time", "5m"]
        assert json.loads((HERE / receipt["limits"]).read_text()) == LIMITS
        if "source" in receipt:
            assert sha(HERE / receipt["source"]) == receipt["sha256"]
    for stem in [selected["strict"]] + selected["constructed_strict"]:
        assert not (HERE / (stem + ".log")).read_bytes(), stem
    canonical = (HERE / (selected["canonical"] + ".log")).read_text()
    assert "Build completed successfully" in canonical
    assert not re.search(r"warning:|error:", canonical)
    spec = importlib.util.spec_from_file_location("deletion_filter_probes", HERE / "deletion-filter-probe-check.py")
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    for group in selected["groups"]:
        probes.check_group(group)
    assert production.read_text().count("\ntheorem ") == 2
    for filename, name in [("deletion-filter-kernels.lean", "actual_boundary"),
                           ("deletion-filter-rejection.lean", "old_cache_rejected")]:
        source = (HERE / filename).read_text()
        private = source.split("private theorem checked :\n", 1)[1].split(" := by\n", 1)[0]
        public = source.split("theorem " + name + " :\n", 1)[1].split(" := checked", 1)[0]
        assert private == public
    positive = (HERE / "deletion-filter-positive.lean").read_text()
    private = positive.split("private theorem checked ", 1)[1].split(" := by\n", 1)[0]
    public = positive.split("theorem actual_publications ", 1)[1].split(" := checked smart kind", 1)[0]
    assert private == public
    assert "Heap Correct reader" in positive
    assert "done smart kind false,done smart kind true" in positive
    assert manifest["groups"] == selected["groups"]
    print(json.dumps({"status": "PASS", "entries": len(manifest["entries"]),
        "public_pairs": 2, "constructed_pairs": 3, "auxiliary_pairs": 0,
        "owned_lean_runs": 16, "scope": "exact singleton filter bridge; checked old-cache exclusion and six actual cold/warm positive publication cases; general publication law remains open"}, sort_keys=True))


if __name__ == "__main__":
    main()
