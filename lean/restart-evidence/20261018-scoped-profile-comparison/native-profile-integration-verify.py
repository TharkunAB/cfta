import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LIMITS = {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def receipt(stem, expected):
    meta = json.loads((HERE / (stem + ".json")).read_text())
    assert meta["exit_code"] == expected, stem
    assert meta["wrapper"][:5] == ["/home/tritlo/Code/heavy-management/bin/capped", "--mem", "4G", "--time", "5m"]
    assert json.loads((HERE / meta["limits"]).read_text()) == LIMITS
    if "source" in meta:
        assert sha(HERE / meta["source"]) == meta["sha256"]
    return meta


def main():
    manifest = json.loads((HERE / "native-profile-integration-manifest.json").read_text())
    for entry in manifest["entries"]:
        path = ROOT / entry["path"]
        assert path.stat().st_size == entry["bytes"] and sha(path) == entry["sha256"], path
    selected = json.loads((HERE / "native-profile-integration-selection.json").read_text())
    assert selected["finalized"] and selected["constructed_pairs"] == 1
    assert selected["owned_public_pairs"] == selected["auxiliary_pairs"] == 0
    assert selected["reused_public_pairs"] == 3
    strict = receipt(selected["strict"], 0)
    assert not (HERE / strict["log"]).read_bytes()
    assert sha(HERE / strict["source"]) == sha(HERE / "native-profile-integration-kernels.lean")
    for attempt in selected["retained_attempts"]:
        receipt(attempt["stem"], attempt["exit_code"])
    for source in selected["reviewed_productions"]:
        assert sha(ROOT / source["path"]) == source["sha256"]
        direct = receipt(source["strict"], 0)
        assert direct["sha256"] == source["sha256"] and not (HERE / direct["log"]).read_bytes()
        canonical = receipt(source["canonical"], 0)
        log = (HERE / canonical["log"]).read_text()
        assert "Build completed successfully" in log and "warning:" not in log and "error:" not in log
    spec = importlib.util.spec_from_file_location("native_profile_integration_probes", HERE / "native-profile-integration-probe-check.py")
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    for group in selected["groups"] + selected["reviewed_groups"]:
        receipt(group["name"], 0)
        probes.check_group(group)
    fixture = (HERE / strict["source"]).read_text()
    first = fixture.split("private theorem checked :\n",1)[1].split(" := by\n",1)[0]
    second = fixture.split("theorem actual_binder_returns :\n",1)[1].split(" := checked",1)[0]
    assert first == second
    for call in ["SourceCurrentNativeBinderProfile.build_profile", "SourceCurrentStoredMuFinishProfile.complete", "SourceCurrentStoredMuFinishProfile.finish_profile"]:
        assert call in fixture
    assert "private theorem heap (smart used : Bool) : Heap Correct (reader smart used)" in fixture
    assert "repeat' first | split at installed | cases installed" in fixture
    assert "∀ smart used : Bool" in first and "∀ warm : Bool" in first
    assert manifest["groups"] == selected["groups"]
    print(json.dumps({"status": "PASS", "entries": len(manifest["entries"]),
        "owned_public_pairs": 0, "constructed_pairs": 1, "auxiliary_pairs": 0,
        "reused_public_pairs": 3, "retained_failed_attempts": 5, "retained_successful_prefixes": 1,
        "scope": "actual raw/smart and bare/used cold/warm binder calls with internally derived final Correct heaps"}, sort_keys=True))


if __name__ == "__main__":
    main()
