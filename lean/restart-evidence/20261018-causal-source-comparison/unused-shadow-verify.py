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
    manifest = json.loads((HERE / "unused-shadow-manifest.json").read_text())
    for entry in manifest["entries"]:
        path = ROOT / entry["path"]
        assert path.stat().st_size == entry["bytes"] and sha(path) == entry["sha256"], path
    selected = json.loads((HERE / "unused-shadow-selection.json").read_text())
    assert selected["finalized"] and selected["owned_lean_runs"] == 6
    assert [selected[k] for k in ["public_pairs", "constructed_pairs", "auxiliary_pairs"]] == [1, 1, 0]
    assert sha(ROOT / selected["production"]) == selected["sha256"]
    strict = json.loads((HERE / (selected["strict"] + ".json")).read_text())
    assert strict["sha256"] == selected["sha256"]
    stems = [selected["strict"], selected["canonical"], selected["constructed_strict"]]
    stems += [g["name"] for g in selected["groups"]] + [i["stem"] for i in selected["retained_unselected"]]
    for stem in stems:
        meta = json.loads((HERE / (stem + ".json")).read_text())
        assert meta["exit_code"] == 0
        assert meta["wrapper"][:5] == ["/home/tritlo/Code/heavy-management/bin/capped", "--mem", "4G", "--time", "5m"]
        assert json.loads((HERE / meta["limits"]).read_text()) == LIMITS
        if "source" in meta:
            assert sha(HERE / meta["source"]) == meta["sha256"]
    for stem in [selected["strict"], selected["constructed_strict"]]:
        assert not (HERE / (stem + ".log")).read_bytes()
    canonical = (HERE / (selected["canonical"] + ".log")).read_text()
    assert "Build completed successfully" in canonical and not re.search(r"warning:|error:", canonical)
    spec = importlib.util.spec_from_file_location("unused_shadow_probes", HERE / "unused-shadow-probe-check.py")
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    for group in selected["groups"]:
        probes.check_group(group)
    source = (ROOT / selected["production"]).read_text()
    assert source.count("\ntheorem ") == 1
    assert "SourceCurrentNativeReaderUnusedRootDeletion.build" in source
    assert "SourceCurrentNativeCallbackErasure.callback_result" in source
    fixture = (HERE / "unused-shadow-kernels.lean").read_text()
    private = fixture.split("private theorem checked ", 1)[1].split(" := by\n", 1)[0]
    public = fixture.split("theorem actual_unused_shadow ", 1)[1].split(" := checked kind warm", 1)[0]
    assert private == public and "common.nodes.next = reader.nodes.next + 1" in public
    assert "SourceCurrentNativeUnusedRootShadow.build" in fixture
    assert manifest["groups"] == selected["groups"]
    print(json.dumps({"status": "PASS", "entries": len(manifest["entries"]), "public_pairs": 1,
        "constructed_pairs": 1, "auxiliary_pairs": 0, "owned_lean_runs": 6,
        "scope": "actual unused return shadow independence and Empty-local strict raw reduction at a source-extended reader"}, sort_keys=True))


if __name__ == "__main__":
    main()
