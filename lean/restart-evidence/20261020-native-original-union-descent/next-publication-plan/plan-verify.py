import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def verify(base, item):
    data = (base / item["path"]).read_bytes()
    assert len(data) == item["bytes"], item["path"]
    assert hashlib.sha256(data).hexdigest() == item["sha256"], item["path"]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((HERE / "plan-manifest.json").read_text())
    assert manifest["kind"] == "unproved-design"
    for item in manifest["files"]:
        verify(HERE, item)
    for item in manifest["sources"]:
        verify(args.root, item)
    pins = json.loads((HERE / "plan-source-pins.json").read_text())
    assert pins["files"] == manifest["sources"]
    plan = (HERE / "plan.md").read_text()
    for expected in ["Design only.", "No theorem in this note has been implemented or checked.",
                     "BEFORE the enclosing", "one common finite rooted build trace", "i<j",
                     "precompletion_selected_writers(p)", "same substantive joint-support proof",
                     "two public heads", "not a general native owner-renewal rank"]:
        assert expected in plan, expected
    print(json.dumps({"status": "PASS", "kind": "unproved-design",
                      "pins": len(manifest["files"]) + len(manifest["sources"]),
                      "source_files": len(manifest["sources"]), "local_files": len(manifest["files"]),
                      "lean_jobs": 0, "proof_pairs": 0, "live": args.live}))


if __name__ == "__main__":
    main()
