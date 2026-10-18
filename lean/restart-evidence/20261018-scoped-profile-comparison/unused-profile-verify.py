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
    manifest = json.loads((HERE / "unused-profile-manifest.json").read_text())
    for entry in manifest["entries"]:
        path = ROOT / entry["path"]
        assert path.stat().st_size == entry["bytes"], path
        assert sha(path) == entry["sha256"], path
    selected = json.loads((HERE / "unused-profile-selection.json").read_text())
    assert selected["finalized"] and selected["public_pairs"] == selected["constructed_pairs"] == 1
    assert selected["auxiliary_pairs"] == 0
    assert sha(ROOT / selected["production"]) == selected["sha256"]
    stems = [selected["strict"], selected["canonical"], selected["constructed_strict"]]
    stems += [group["name"] for group in selected["groups"]]
    for stem in stems + [item["stem"] for item in selected["retained_unselected"]]:
        receipt = json.loads((HERE / (stem + ".json")).read_text())
        assert receipt["wrapper"][:5] == ["/home/tritlo/Code/heavy-management/bin/capped", "--mem", "4G", "--time", "5m"]
        assert json.loads((HERE / receipt["limits"]).read_text()) == LIMITS
        if "source" in receipt:
            assert sha(HERE / receipt["source"]) == receipt["sha256"]
        assert receipt["exit_code"] == (0 if stem in stems else 1), stem
    for stem in [selected["strict"], selected["constructed_strict"]]:
        assert not (HERE / (stem + ".log")).read_bytes(), stem
    strict = json.loads((HERE / (selected["strict"] + ".json")).read_text())
    assert strict["sha256"] == selected["sha256"]
    kernel = json.loads((HERE / (selected["constructed_strict"] + ".json")).read_text())
    assert sha(HERE / kernel["source"]) == sha(HERE / "unused-profile-kernels.lean")
    canonical = (HERE / (selected["canonical"] + ".log")).read_text()
    assert "Build completed successfully" in canonical and "warning:" not in canonical and "error:" not in canonical
    spec = importlib.util.spec_from_file_location("unused_profile_probes", HERE / "unused-profile-probe-check.py")
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    for group in selected["groups"]:
        probes.check_group(group)
    source = (ROOT / selected["production"]).read_text()
    assert source.count("\ntheorem ") == 1 and "marker" not in source.split("theorem smart_unused",1)[1]
    assert "(unused : usesLocal depth ordinary = false)" in source
    assert "(depthCorrect false).1" in source and "(depthCorrect true).1" in source
    fixture = (HERE / kernel["source"]).read_text()
    private = fixture.split("private theorem checked :\n",1)[1].split(" := by\n",1)[0]
    public = fixture.split("theorem actual_branches :\n",1)[1].split(" := checked",1)[0]
    assert private == public
    assert "SourceCurrentStoredMuUnusedProfile.smart_unused" in fixture
    assert "SourceCurrentConstrainedCapSourceHistory.empty_context.build" in fixture
    assert "if ordinaryCase then .node [.mk 7 false []] else .var 0" in fixture
    assert manifest["groups"] == selected["groups"]
    print(json.dumps({"status": "PASS", "entries": len(manifest["entries"]),
        "public_pairs": 1, "constructed_pairs": 1, "auxiliary_pairs": 0,
        "retained_failed_attempts": len(selected["retained_unselected"]),
        "scope": "all unused smart cleanup branches reduce to the probe with an Empty local; parametric Correct remains explicit"}, sort_keys=True))


if __name__ == "__main__":
    main()
