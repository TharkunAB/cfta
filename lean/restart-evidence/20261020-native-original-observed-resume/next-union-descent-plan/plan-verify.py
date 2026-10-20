import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREFIX = "plan"


def check(base, item):
    data = (base / item["path"]).read_bytes()
    assert len(data) == item["bytes"], item["path"]
    assert hashlib.sha256(data).hexdigest() == item["sha256"], item["path"]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((HERE / (PREFIX + "-manifest.json")).read_text())
    assert manifest["kind"] == "unproved-design"
    for item in manifest["files"]:
        check(HERE, item)
    for item in manifest["sources"]:
        check(args.root, item)
    pins = json.loads((HERE / (PREFIX + "-source-pins.json")).read_text())
    assert pins["files"] == manifest["sources"]
    plan = (HERE / (PREFIX + ".md")).read_text()
    for expected in ["Design only.", "No theorem in this note has been implemented or checked.",
                     "pure generic predicate", "SAME terminal existential", "base Observed once",
                     "derive terminal and descent together", "SourceRow.union", "originalRow",
                     "Written and Stored remain independent", "global renewal rank"]:
        assert expected in plan, expected
    print(json.dumps({"status": "PASS", "kind": "unproved-design",
                      "pins": len(manifest["files"]) + len(manifest["sources"]),
                      "source_files": len(manifest["sources"]), "local_files": len(manifest["files"]),
                      "lean_jobs": 0, "proof_pairs": 0, "live": args.live}))


if __name__ == "__main__":
    main()
