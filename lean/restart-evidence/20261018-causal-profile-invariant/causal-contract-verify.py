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
    manifest = json.loads((HERE / "causal-contract-manifest.json").read_text())
    for entry in manifest["entries"]:
        path = ROOT / entry["path"]
        assert path.stat().st_size == entry["bytes"], path
        assert sha(path) == entry["sha256"], path
    selected = json.loads((HERE / "causal-contract-selection.json").read_text())
    assert selected["finalized"]
    assert selected["new_lean_runs"] == selected["owned_public_pairs"] == selected["owned_constructed_pairs"] == 0
    assert selected["reused_public_pairs"] == 16 and selected["reused_constructed_pairs"] == 0
    for production in selected["production"]:
        path = ROOT / production["path"]
        assert sha(path) == production["sha256"], path
        strict = json.loads((HERE / (production["strict"] + ".json")).read_text())
        assert strict["exit_code"] == 0 and strict["sha256"] == production["sha256"]
        assert not (HERE / strict["log"]).read_bytes(), production["strict"]
        assert sha(HERE / strict["source"]) == strict["sha256"]
        canonical = json.loads((HERE / (production["canonical"] + ".json")).read_text())
        assert canonical["exit_code"] == 0
        log = (HERE / canonical["log"]).read_text()
        assert "Build completed successfully" in log and "warning:" not in log and "error:" not in log
        for receipt in (strict, canonical):
            assert json.loads((HERE / receipt["limits"]).read_text()) == LIMITS
    spec = importlib.util.spec_from_file_location("causal_contract_probes", HERE / "causal-contract-probe-check.py")
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    for group in selected["groups"]:
        probes.check_group(group)
        receipt = json.loads((HERE / (group["name"] + ".json")).read_text())
        assert sha(HERE / receipt["source"]) == receipt["sha256"]
    assert manifest["groups"] == selected["groups"]
    assert sum(group["pairs"] for group in selected["groups"]) == 16
    print(json.dumps({"status": "PASS", "entries": len(manifest["entries"]),
        "owned_public_pairs": 0, "owned_constructed_pairs": 0,
        "reused_public_pairs": 16, "new_lean_runs": 0,
        "scope": "pure per-payload contract and actual execution bridge audited; general publication law remains unproved"}, sort_keys=True))


if __name__ == "__main__":
    main()
