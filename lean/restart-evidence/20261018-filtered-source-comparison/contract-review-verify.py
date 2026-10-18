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
    manifest = json.loads((HERE / "contract-review-manifest.json").read_text())
    for entry in manifest["entries"]:
        path = ROOT / entry["path"]
        assert path.stat().st_size == entry["bytes"], path
        assert sha(path) == entry["sha256"], path
    selected = json.loads((HERE / "contract-review-selection.json").read_text())
    assert selected["finalized"] and selected["constructed_pairs"] == 2
    assert selected["public_pairs"] == selected["auxiliary_pairs"] == 0
    assert selected["canonical"] is None
    source = HERE / selected["source"]
    assert sha(source) == selected["source_sha256"]
    strict = selected["constructed_strict"]
    assert not (HERE / (strict + ".log")).read_bytes()
    meta = json.loads((HERE / (strict + ".json")).read_text())
    assert meta["sha256"] == selected["source_sha256"]
    assert (HERE / meta["source"]).read_bytes() == source.read_bytes()
    for stem in selected["retained_unselected"] + [strict] + [g["name"] for g in selected["groups"]]:
        receipt = json.loads((HERE / (stem + ".json")).read_text())
        assert receipt["wrapper"][:5] == ["/home/tritlo/Code/heavy-management/bin/capped", "--mem", "4G", "--time", "5m"]
        assert json.loads((HERE / receipt["limits"]).read_text()) == LIMITS
        assert sha(HERE / receipt["source"]) == receipt["sha256"]
        expected = 1 if stem in {"contract-review-direct-1", "contract-review-full-1", "contract-review-full-2", "contract-review-full-3", "contract-review-full-4"} else 0
        assert receipt["exit_code"] == expected, stem
    spec = importlib.util.spec_from_file_location("contract_review_probes", HERE / "contract-review-probe-check.py")
    probes = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(probes)
    for group in selected["groups"]:
        probes.check_group(group)
    text = source.read_text()
    assert text.count("\ntheorem ") == 2
    assert "theorem actual_source_filter_boundary" in text
    assert "theorem correct_does_not_control_filter" in text
    assert "Context state [] ∧ Ready state ∧ Available" in text
    assert "SourceCurrentPublicationHeapInduction.Heap Correct state" in text
    assert "(∀ assignment, Equivalent (denote left assignment) (denote right assignment))" in text
    assert manifest["groups"] == selected["groups"]
    print(json.dumps({"status": "PASS", "entries": len(manifest["entries"]),
        "production_pairs": 0, "constructed_pairs": 2, "auxiliary_pairs": 0,
        "owned_lean_runs": 9, "failed_attempts": 5,
        "scope": "local root-filter noncongruence with actual source calls and a fully summary-correct resident heap; complete source Law unrefuted"}, sort_keys=True))


if __name__ == "__main__":
    main()
