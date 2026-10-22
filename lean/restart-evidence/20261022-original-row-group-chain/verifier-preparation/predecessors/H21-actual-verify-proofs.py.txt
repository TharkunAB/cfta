"""Check saved prepend-grouping evidence. This script does not run Lean."""
import argparse
import difflib
import hashlib
import json
import re
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--root", required=True, type=Path)
parser.add_argument("--live", action="store_true")
args = parser.parse_args()
root = args.root.resolve()
evidence = root / "lean/restart-evidence/20261022-prepend-grouping"
def load(name):
    return json.loads((evidence / name).read_text())
def digest(data):
    return hashlib.sha256(data).hexdigest()
def canonical(text):
    return re.sub(r"[ \t\r\n]+", " ", text).strip(" \t\r\n")
name = "SourceCurrentPrependGrouping"
namespace = "MicroCFTA." + name + "."
specs = [("insertWith", "def"), ("fromRows", "def"), ("reverseTable", "def"),
    ("pair_fold", "theorem"), ("reverse_insert_singleton", "theorem"), ("reverse_fold", "theorem"),
    ("reverse_fromRows", "theorem"), ("iteration_reverse", "theorem"), ("iteration_permutation", "theorem")]
short_names = [short for short, kind in specs]
selected_sha = "3d293c27b502aa308c8cc05f21796264b18f873221b3343910e77d6bcb6b53ba"
source_lines = int("89")
strict_stem, full_stem, audit_stem = "prepend-grouping-strict-3", "prepend-grouping-public-1", "prepend-grouping-audit-1"
metrics = dict(actual_jobs=int("5"), source_jobs=int("4"), audit_jobs=int("1"),
    failed_jobs=int("2"), warned_source_exit_zero_jobs=int("0"),
    rejected_public_type_jobs=int("0"))
jobs = json.loads('{"prepend-grouping-audit-1": [0, null, "ac7c811b03802079e982a193b2256289c418f7c5449cc52176ddaaa107580fff", 0, 0], "prepend-grouping-public-1": [0, "0744a37546ea7fa5c6576dd5cf4b6268137219fe68829438f0a8c54e31332015", "215b81824a227e47375a236476dd83092a5bf1c21a421a85e835bdd3e75e61a8", 0, 0], "prepend-grouping-strict-1": [1, "e902b0688085906c13d7150f11e55b1ae181cecadba32a2f9584149c717c089a", "34a9860d3c5a16abe344014ebe8d273d5068cb568fe8150a2aa6bea14aafa14c", 4, 0], "prepend-grouping-strict-2": [1, "129214eaeba41547a747f3b25e807c04da107a4b130f3a68f78b79a26449a328", "77d0d466713ae4130492b7d0d6458db2fc651d33b6e62bd35fc8b12d4002501e", 1, 0], "prepend-grouping-strict-3": [0, "3d293c27b502aa308c8cc05f21796264b18f873221b3343910e77d6bcb6b53ba", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", 0, 0]}')
rejected = json.loads('[]')
assert re.fullmatch(r"[0-9a-f]{64}", selected_sha)
assert jobs and all(stem.startswith("prepend-grouping-") for stem in jobs)
assert strict_stem in jobs and full_stem in jobs and audit_stem in jobs
assert jobs[strict_stem][0] == jobs[full_stem][0] == jobs[audit_stem][0] == 0
assert jobs[strict_stem][1] == selected_sha and jobs[strict_stem][3:] == jobs[full_stem][3:] == [0, 0]
assert (evidence / (audit_stem + ".json")).is_file(), "Audit is pending; no complete proof report is available"
actual = set()
for path in evidence.glob("*.json"):
    item = json.loads(path.read_text())
    if isinstance(item, dict) and "wrapper" in item and "exit_code" in item:
        if Path(item.get("command", [""])[0]).name in {"lean", "lake"}:
            actual.add(path.stem)
assert actual == set(jobs), actual
assert metrics["actual_jobs"] == len(actual) and metrics["source_jobs"] == sum(bool(row[1]) for row in jobs.values())
assert metrics["audit_jobs"] == sum(not row[1] for row in jobs.values()) and jobs[audit_stem][1] is None
assert metrics["failed_jobs"] == sum(row[0] != 0 for row in jobs.values())
assert metrics["warned_source_exit_zero_jobs"] == sum(row[0] == 0 and bool(row[1]) and bool(row[4]) for row in jobs.values())
assert len(rejected) == len(set(rejected)) == metrics["rejected_public_type_jobs"] and full_stem not in rejected
assert all(stem in jobs and "public" in stem and jobs[stem][0] == 0 for stem in rejected)
public_hashes = [row[1] for stem, row in jobs.items() if row[1] and "public" in stem]
assert len(public_hashes) == len(set(public_hashes)), "FULL repeated on an unchanged source variant"
for stem, (exit_code, source_hash, log_hash, errors, warnings) in jobs.items():
    receipt = load(stem + ".json")
    assert receipt["exit_code"] == exit_code and receipt["log"] == stem + ".log" and receipt["observed_at"]
    raw = (evidence / receipt["log"]).read_bytes()
    assert re.fullmatch(r"[0-9a-f]{64}", log_hash) and digest(raw) == log_hash, stem
    assert receipt["limits"] == stem + ".limits.json"
    assert load(receipt["limits"]) == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
    usage = load(stem + ".usage.json")
    assert 0 <= usage["age_seconds"] <= 600 and usage["remaining_percent"] > 1, stem
    assert receipt["wrapper"][1:5] == ["--mem", "4G", "--time", "5m"]
    if source_hash:
        assert receipt["source"] == stem + ".source.lean" and receipt["sha256"] == source_hash
        source = (evidence / receipt["source"]).read_bytes()
        assert digest(source) == source_hash and Path(receipt["command"][-1]).resolve() == (evidence / receipt["source"]).resolve()
        assert len(receipt["command"]) == 3 and Path(receipt["command"][0]).name == "lean" and receipt["command"][1] == "-Dlinter.all=true"
        assert len(re.findall(r"^.+?:\d+:\d+: error(?:\([^)]*\))?:", raw.decode(), re.M)) == errors
        assert len(re.findall(r"^.+?:\d+:\d+: warning(?:\([^)]*\))?:", raw.decode(), re.M)) == warnings
        if "public" not in stem:
            assert not re.search(r"^\s*set_option (?:maxHeartbeats|maxRecDepth|linter\.)", source.decode(), re.M)
    else:
        assert Path(receipt["command"][0]).name == "lake" and receipt["command"][-2:] == ["build", "MicroCFTA.Audit"]
strict_source = (evidence / (strict_stem + ".source.lean")).read_bytes()
assert len(strict_source.splitlines()) == source_lines <= 240
assert (evidence / (strict_stem + ".log")).read_bytes() == b""
selection = load("selected-sources.json")
source_path = "lean/MicroCFTA/" + name + ".lean"
assert selection == {source_path: dict(sha256=selected_sha, lines=source_lines, strict=strict_stem, full=full_stem)}
source = (evidence / (name + ".lean")).read_bytes()
assert digest(source) == selected_sha and source == strict_source
gate = load("selected-source-gate.json")
assert gate == dict(status="ROOT_ACCEPTED", path=source_path, sha256=selected_sha, lines=source_lines, snapshot="selected-sources/" + name + ".lean")
assert (evidence / gate["snapshot"]).read_bytes() == source
history = load("source-history-gate.json")
assert history == json.loads('{"status": "ROOT_ACCEPTED", "selected_source_sha256": "3d293c27b502aa308c8cc05f21796264b18f873221b3343910e77d6bcb6b53ba", "variants": [{"path": "source-proposal/SourceCurrentPrependGrouping.lean", "sha256": "c912103bcc9f07527f93f167683ab45100436fdaa9cd0db6c0d896ed4202546b", "lines": 85, "reason": "Uncompiled proposal retained after source review found lookup normalization issue."}, {"path": "source-proposal-v2/SourceCurrentPrependGrouping.lean", "sha256": "e902b0688085906c13d7150f11e55b1ae181cecadba32a2f9584149c717c089a", "lines": 85, "reason": "One lookup-case repair; actual strict1 failed with four errors."}, {"path": "source-proposal-v3/SourceCurrentPrependGrouping.lean", "sha256": "129214eaeba41547a747f3b25e807c04da107a4b130f3a68f78b79a26449a328", "lines": 85, "reason": "Four error repairs; actual strict2 failed at empty-table function equality."}, {"path": "source-proposal-v4/SourceCurrentPrependGrouping.lean", "sha256": "3d293c27b502aa308c8cc05f21796264b18f873221b3343910e77d6bcb6b53ba", "lines": 89, "reason": "Repair empty-table function equality; strict3 clean and sole FULL1 passed."}, {"path": "prepend-grouping-strict-1.source.lean", "sha256": "e902b0688085906c13d7150f11e55b1ae181cecadba32a2f9584149c717c089a", "lines": 85, "reason": "Exact actual ordinary-check input: prepend-grouping-strict-1"}, {"path": "prepend-grouping-strict-2.source.lean", "sha256": "129214eaeba41547a747f3b25e807c04da107a4b130f3a68f78b79a26449a328", "lines": 85, "reason": "Exact actual ordinary-check input: prepend-grouping-strict-2"}, {"path": "prepend-grouping-strict-3.source.lean", "sha256": "3d293c27b502aa308c8cc05f21796264b18f873221b3343910e77d6bcb6b53ba", "lines": 89, "reason": "Exact actual ordinary-check input: prepend-grouping-strict-3"}], "artifacts": [{"path": "full-preparation-v2/actual-failed-reader-1/mcfta-prepend-grouping-read-full-1.json", "sha256": "86597ee0334aa110a3d9672339ec906aadc58d50f08ebf6be682cd8b6097bbe8", "bytes": 1315}, {"path": "full-preparation-v2/actual-failed-reader-1/mcfta-prepend-grouping-read-full-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3", "bytes": 90}, {"path": "full-preparation-v2/actual-failed-reader-1/mcfta-prepend-grouping-read-full-1.log", "sha256": "5ca2900359684d98def22d4c0bb34ad06aa212ace581908acc099d711fcbed3e", "bytes": 318}, {"path": "full-preparation-v2/actual-failed-reader-1/mcfta-prepend-grouping-read-full-1.peaks.txt", "sha256": "853f76e29e888ad06e5cfb363577bac4ea2912c217669885f287816ecbdcdcd2", "bytes": 37}, {"path": "full-preparation-v2/actual-failed-reader-1/mcfta-prepend-grouping-read-full-1.source.py", "sha256": "53ad8cc4f0cfa01ee0341f7d7ea62bced10b068d20584058104a26509a2345ad", "bytes": 7993}, {"path": "full-preparation-v2/actual-failed-reader-1/mcfta-prepend-grouping-read-full-1.usage.json", "sha256": "0f716f2902e40947ec976237a35ed3db5f72fd787b67feb06df3387ff43f9c84", "bytes": 114}, {"path": "full-public-audit/actual-reader-metadata/mcfta-prepend-grouping-read-full-1.json", "sha256": "86597ee0334aa110a3d9672339ec906aadc58d50f08ebf6be682cd8b6097bbe8", "bytes": 1315}, {"path": "full-public-audit/actual-reader-metadata/mcfta-prepend-grouping-read-full-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3", "bytes": 90}, {"path": "full-public-audit/actual-reader-metadata/mcfta-prepend-grouping-read-full-1.log", "sha256": "5ca2900359684d98def22d4c0bb34ad06aa212ace581908acc099d711fcbed3e", "bytes": 318}, {"path": "full-public-audit/actual-reader-metadata/mcfta-prepend-grouping-read-full-1.peaks.txt", "sha256": "853f76e29e888ad06e5cfb363577bac4ea2912c217669885f287816ecbdcdcd2", "bytes": 37}, {"path": "full-public-audit/actual-reader-metadata/mcfta-prepend-grouping-read-full-1.source.py", "sha256": "53ad8cc4f0cfa01ee0341f7d7ea62bced10b068d20584058104a26509a2345ad", "bytes": 7993}, {"path": "full-public-audit/actual-reader-metadata/mcfta-prepend-grouping-read-full-1.usage.json", "sha256": "0f716f2902e40947ec976237a35ed3db5f72fd787b67feb06df3387ff43f9c84", "bytes": 114}, {"path": "full-public-audit/actual-reader-metadata/mcfta-prepend-grouping-read-full-2.json", "sha256": "a5ee02aad97b7083542b4f71f25162b03954341d707303404b7882a1e90fd134", "bytes": 1318}, {"path": "full-public-audit/actual-reader-metadata/mcfta-prepend-grouping-read-full-2.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3", "bytes": 90}, {"path": "full-public-audit/actual-reader-metadata/mcfta-prepend-grouping-read-full-2.log", "sha256": "e1e4d6ea37109a5b9ed86edb3422d72dcb330b66fdb82456e838defd5081d8b1", "bytes": 18154}, {"path": "full-public-audit/actual-reader-metadata/mcfta-prepend-grouping-read-full-2.peaks.txt", "sha256": "22c1426ce326b023ea17ac1a67c520b913b1944134b5b829f3c157aacd5b8da0", "bytes": 36}, {"path": "full-public-audit/actual-reader-metadata/mcfta-prepend-grouping-read-full-2.source.py", "sha256": "3f88ecfe2662cc630dc73caee5c3862970f51e405344e2d6e14f29c82de9459e", "bytes": 8525}, {"path": "full-public-audit/actual-reader-metadata/mcfta-prepend-grouping-read-full-2.usage.json", "sha256": "0d7b2b445a9d26d13f320fbb97c0ba5f1b337f2fb170feb4f9e902768477cea4", "bytes": 114}, {"path": "prepend-grouping-audit-1.json", "sha256": "1817915afd44802b8810fadc8e521de3ba915efa43cc188316d9868c4dc649aa", "bytes": 577}, {"path": "prepend-grouping-audit-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3", "bytes": 90}, {"path": "prepend-grouping-audit-1.log", "sha256": "ac7c811b03802079e982a193b2256289c418f7c5449cc52176ddaaa107580fff", "bytes": 685}, {"path": "prepend-grouping-audit-1.usage.json", "sha256": "fa97dc7f419ca9a45a776517c54b674880660ca849e5c4652de9de6ea741bbb3", "bytes": 114}, {"path": "prepend-grouping-public-1.json", "sha256": "6b4fc0ee91d420866a78b11336f9625947f01d27db28918b12a048431d5771e9", "bytes": 772}, {"path": "prepend-grouping-public-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3", "bytes": 90}, {"path": "prepend-grouping-public-1.log", "sha256": "215b81824a227e47375a236476dd83092a5bf1c21a421a85e835bdd3e75e61a8", "bytes": 133490}, {"path": "prepend-grouping-public-1.source.lean", "sha256": "0744a37546ea7fa5c6576dd5cf4b6268137219fe68829438f0a8c54e31332015", "bytes": 6495}, {"path": "prepend-grouping-public-1.usage.json", "sha256": "60da57c65a99a3d92d091ced7a9e69b0bd174a7f065d39cf7db2c53b8b4e19d1", "bytes": 114}, {"path": "prepend-grouping-strict-1.json", "sha256": "4eec31dec453cdb2ee2aff6def86342f468fbaa8809f7c7c53c076b9b167cc3a", "bytes": 772}, {"path": "prepend-grouping-strict-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3", "bytes": 90}, {"path": "prepend-grouping-strict-1.log", "sha256": "34a9860d3c5a16abe344014ebe8d273d5068cb568fe8150a2aa6bea14aafa14c", "bytes": 2333}, {"path": "prepend-grouping-strict-1.usage.json", "sha256": "58478f1bbaeac365aa594eb8157da94405f11059474826b5159f39fd3f9e2d37", "bytes": 114}, {"path": "prepend-grouping-strict-2.json", "sha256": "944bcc5f74dde11917dbf76d216769eac04c7911a54f104d9d55e5c2f9de5a4d", "bytes": 772}, {"path": "prepend-grouping-strict-2.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3", "bytes": 90}, {"path": "prepend-grouping-strict-2.log", "sha256": "77d0d466713ae4130492b7d0d6458db2fc651d33b6e62bd35fc8b12d4002501e", "bytes": 755}, {"path": "prepend-grouping-strict-2.usage.json", "sha256": "d285ac32829512a439827c2ade851f1fbaaebd3cb6d451fe0c181fbcbd176304", "bytes": 114}, {"path": "prepend-grouping-strict-3.json", "sha256": "4bda489a96fac57cfc5236a1ae0dd6bf2d62f33bd10769dc488491618aecf39d", "bytes": 772}, {"path": "prepend-grouping-strict-3.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3", "bytes": 90}, {"path": "prepend-grouping-strict-3.log", "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", "bytes": 0}, {"path": "prepend-grouping-strict-3.usage.json", "sha256": "6a60e671d4abf2e9c30bd5f50eb237b983bdc6b097c926fb9e7280577e03821c", "bytes": 114}, {"path": "root-full-review.json", "sha256": "4018556a84417d59c418602336c6357a162f0a3e535589f4ebf064d505add3e0", "bytes": 4305}, {"path": "root-peaks.txt", "sha256": "a572b373b5fe806d2c7a03323a7840a72ed75af1d5eaef02771944087aa97084", "bytes": 190}, {"path": "root-reader-v2-review.json", "sha256": "56d097f8b15a3dd5977858ece5b2c8107779891117d95d5bd2bb9e21c7366254", "bytes": 448}, {"path": "signature-plan/context.lean.txt", "sha256": "50a6a280046eea149e67e07683153558840c8bd7e5465104d32bd8f1e230cdda", "bytes": 172}, {"path": "signature-plan/declarations.lean.txt", "sha256": "c903f09c4f52b0db58dd5c94dbb85e765d5d84905666bc4f9216f567c16c333f", "bytes": 2536}, {"path": "signature-plan/definition-equations.md", "sha256": "1577ab7051923b766957b280526fee7ea2cc6e002bfadfbffac40900685fe66b", "bytes": 954}, {"path": "signature-plan/definition-headers.lean.txt", "sha256": "bc4943d091a3ff7dd4ab00c0d040225b7ea5d70b5912b9c96256103f9030eb95", "bytes": 440}, {"path": "signature-plan/local-induction.lean.txt", "sha256": "e7ef37d2674fbf1bf27a39cb08e1400c847b849b0f7b680c5fb8206411ab7a89", "bytes": 402}, {"path": "signature-plan/proposed-signatures.lean.txt", "sha256": "3245fa39aacaa0c109913a82f296b58468b01d60a2d8fb4467a5cfd23e7653b2", "bytes": 1879}, {"path": "source-proposal-v2/precheck-lookup-normalization.patch", "sha256": "2630f37d1642d9151a850c2e2149526736ef9ea0210504eee920faa9511e1992", "bytes": 508}, {"path": "source-proposal-v3/four-error-repair.patch", "sha256": "e47fdb8946dd250ed88f0a7bd504a1abfece5a823c69aad7e0e3d8dd9dca2222", "bytes": 2170}, {"path": "source-proposal-v4/empty-table-function-repair.patch", "sha256": "111c89b1060da401fadd543f586ccaed1eb01b5a90862408cca0b2f07afaea63", "bytes": 929}], "patches": [{"reason": "Use the normalized rowKey lookup case.", "before": "source-proposal/SourceCurrentPrependGrouping.lean", "after": "source-proposal-v2/SourceCurrentPrependGrouping.lean", "path": "source-proposal-v2/precheck-lookup-normalization.patch", "sha256": "2630f37d1642d9151a850c2e2149526736ef9ea0210504eee920faa9511e1992", "fromfile": "v1/SourceCurrentPrependGrouping.lean", "tofile": "v2/SourceCurrentPrependGrouping.lean"}, {"reason": "Repair four actual strict1 elaboration errors.", "before": "source-proposal-v2/SourceCurrentPrependGrouping.lean", "after": "source-proposal-v3/SourceCurrentPrependGrouping.lean", "path": "source-proposal-v3/four-error-repair.patch", "sha256": "e47fdb8946dd250ed88f0a7bd504a1abfece5a823c69aad7e0e3d8dd9dca2222", "fromfile": "v2/SourceCurrentPrependGrouping.lean", "tofile": "v3/SourceCurrentPrependGrouping.lean"}, {"reason": "Repair the remaining actual strict2 empty-table equality.", "before": "source-proposal-v3/SourceCurrentPrependGrouping.lean", "after": "source-proposal-v4/SourceCurrentPrependGrouping.lean", "path": "source-proposal-v4/empty-table-function-repair.patch", "sha256": "111c89b1060da401fadd543f586ccaed1eb01b5a90862408cca0b2f07afaea63", "fromfile": "v3/SourceCurrentPrependGrouping.lean", "tofile": "v4/SourceCurrentPrependGrouping.lean"}], "rejected_public_types": []}') and history["status"] == "ROOT_ACCEPTED"
assert history["selected_source_sha256"] == selected_sha
assert set(history) == {"status", "selected_source_sha256", "variants", "artifacts", "patches", "rejected_public_types"}
variants = {item["path"]: item for item in history["variants"]}
artifacts = {item["path"]: item for item in history["artifacts"]}
assert variants and len(variants) == len(history["variants"]) and len(artifacts) == len(history["artifacts"])
for path, item in {**artifacts, **variants}.items():
    relative = Path(path)
    assert not relative.is_absolute() and ".." not in relative.parts
    data = (evidence / relative).read_bytes()
    assert re.fullmatch(r"[0-9a-f]{64}", item["sha256"]) and digest(data) == item["sha256"]
    if path in variants:
        assert 0 < len(data.splitlines()) == item["lines"] <= 240 and isinstance(item["reason"], str) and item["reason"].strip()
    else:
        assert len(data) == item["bytes"]
assert not set(variants) & set(artifacts)
for stem, row in jobs.items():
    for suffix in [".json", ".log", ".limits.json", ".usage.json"]:
        assert stem + suffix in artifacts, ("unretained actual job artifact", stem, suffix)
    if row[1] and "public" in stem:
        assert stem + ".source.lean" in artifacts, "FULL printer sources are artifacts, not bounded math variants"
assert any((evidence / path).read_bytes() == source for path in variants)
for stem, row in jobs.items():
    if row[1] and "public" not in stem:
        assert any(pin["sha256"] == row[1] and (evidence / path).read_bytes() == (evidence / (stem + ".source.lean")).read_bytes() for path, pin in variants.items()), stem
for patch in history["patches"]:
    assert isinstance(patch["reason"], str) and patch["reason"].strip()
    assert patch["before"] in variants and patch["after"] in variants
    assert patch["path"] in artifacts and artifacts[patch["path"]]["sha256"] == patch["sha256"]
    before, after = [(evidence / patch[key]).read_text() for key in ["before", "after"]]
    expected = "".join(difflib.unified_diff(before.splitlines(True), after.splitlines(True), fromfile=patch["fromfile"], tofile=patch["tofile"]))
    assert (evidence / patch["path"]).read_text() == expected
rejections = {item["stem"]: item for item in history["rejected_public_types"]}
assert len(rejections) == len(history["rejected_public_types"]) and set(rejections) == set(rejected)
for stem, item in rejections.items():
    assert item["raw_sha256"] == jobs[stem][2] and item["reason"] and item["artifacts"]
    assert all(path in artifacts for path in item["artifacts"])
contracts = json.loads('{"context.lean.txt": {"path": "signature-plan/context.lean.txt", "sha256": "50a6a280046eea149e67e07683153558840c8bd7e5465104d32bd8f1e230cdda", "lines": 6}, "declarations.lean.txt": {"path": "signature-plan/declarations.lean.txt", "sha256": "c903f09c4f52b0db58dd5c94dbb85e765d5d84905666bc4f9216f567c16c333f", "lines": 49}, "definition-headers.lean.txt": {"path": "signature-plan/definition-headers.lean.txt", "sha256": "bc4943d091a3ff7dd4ab00c0d040225b7ea5d70b5912b9c96256103f9030eb95", "lines": 9}, "proposed-signatures.lean.txt": {"path": "signature-plan/proposed-signatures.lean.txt", "sha256": "3245fa39aacaa0c109913a82f296b58468b01d60a2d8fb4467a5cfd23e7653b2", "lines": 31}, "local-induction.lean.txt": {"path": "signature-plan/local-induction.lean.txt", "sha256": "e7ef37d2674fbf1bf27a39cb08e1400c847b849b0f7b680c5fb8206411ab7a89", "lines": 6}, "definition-equations.md": {"path": "signature-plan/definition-equations.md", "sha256": "1577ab7051923b766957b280526fee7ea2cc6e002bfadfbffac40900685fe66b", "lines": 8}}')
expected_contracts = {'context.lean.txt': {'path': 'signature-plan/context.lean.txt', 'sha256': '50a6a280046eea149e67e07683153558840c8bd7e5465104d32bd8f1e230cdda', 'lines': 6}, 'declarations.lean.txt': {'path': 'signature-plan/declarations.lean.txt', 'sha256': 'c903f09c4f52b0db58dd5c94dbb85e765d5d84905666bc4f9216f567c16c333f', 'lines': 49}, 'definition-headers.lean.txt': {'path': 'signature-plan/definition-headers.lean.txt', 'sha256': 'bc4943d091a3ff7dd4ab00c0d040225b7ea5d70b5912b9c96256103f9030eb95', 'lines': 9}, 'proposed-signatures.lean.txt': {'path': 'signature-plan/proposed-signatures.lean.txt', 'sha256': '3245fa39aacaa0c109913a82f296b58468b01d60a2d8fb4467a5cfd23e7653b2', 'lines': 31}, 'local-induction.lean.txt': {'path': 'signature-plan/local-induction.lean.txt', 'sha256': 'e7ef37d2674fbf1bf27a39cb08e1400c847b849b0f7b680c5fb8206411ab7a89', 'lines': 6}, 'definition-equations.md': {'path': 'signature-plan/definition-equations.md', 'sha256': '1577ab7051923b766957b280526fee7ea2cc6e002bfadfbffac40900685fe66b', 'lines': 8}}
assert contracts == expected_contracts and list(contracts) == list(expected_contracts)
contract_data = {}
for filename, item in contracts.items():
    relative = Path(item["path"])
    assert not relative.is_absolute() and ".." not in relative.parts
    data = (evidence / relative).read_bytes()
    assert digest(data) == item["sha256"] and len(data.splitlines()) == item["lines"]
    contract_data[filename] = data
context, proposed = contract_data["context.lean.txt"], contract_data["declarations.lean.txt"]
assert source.startswith(context) and proposed.startswith(context)
markers = list(re.finditer(rb"(?m)^/--[^\n]*-/\n(def|theorem) ([^\s(\[{:=]+)", proposed))
assert [(m.group(2).decode(), m.group(1).decode()) for m in markers] == specs
positions = []
for index, marker in enumerate(markers):
    end = markers[index + 1].start() if index + 1 < len(markers) else proposed.rindex(b"\nend MicroCFTA.")
    header = proposed[marker.start():end].rstrip(b"\n") + (b" :=\n" if specs[index][1] == "def" else b" := by\n")
    assert source.count(header) == 1 and source.index(header) >= len(context)
    positions.append(source.index(header))
assert positions == sorted(set(positions))
public = re.findall(r"(?m)^\s*(?:(?:noncomputable|unsafe|partial)\s+)?(def|theorem|lemma|abbrev|opaque|instance|structure|inductive)\s+([^\s(\[{:=]+)", source.decode())
assert public == [(kind, short) for short, kind in specs]
helpers = []
for line in source.decode().splitlines():
    if re.match(r"^\s*(?:(?:noncomputable|unsafe|partial)\s+)?private\b", line):
        declaration = re.match(r"^\s*(?:(?:noncomputable|unsafe|partial)\s+)?private\s+(?:(?:noncomputable|unsafe|partial)\s+)?(?:def|theorem|lemma|abbrev|opaque|instance|structure|inductive)\s+([^\s(\[{:=]+)", line)
        assert declaration, ("unsupported private declaration", line)
        helpers.append(declaration.group(1))
assert helpers == [], "The approved H21 source has no private declarations"
declaration_review = load("root-declaration-review.json")
assert declaration_review["status"] == "ROOT_DECLARATION_REVIEW_CLEAR"
assert declaration_review["definitions"] == short_names[:3] and declaration_review["public_theorems"] == short_names[3:]
assert declaration_review["private_helpers"] == [] and declaration_review["hard_stop_lines"] == 240
if args.live:
    assert (root / source_path).read_bytes() == source
original = (evidence / "original-sources/Audit.original.lean.txt").read_bytes()
assert digest(original) == "69e0e42c6e36fbe4cf9868df0582642fe2bf2a6df7c1ad3af4fae169445f6dd3" and len(original.splitlines()) == 3126
assert load("original-source-index.json")["sources"] == [dict(path="lean/MicroCFTA/Audit.lean", snapshot="original-sources/Audit.original.lean.txt", lines=3126, sha256=digest(original))]
addition = b"import MicroCFTA.SourceCurrentPrependGrouping\n"
audit_source = (root / "lean/MicroCFTA/Audit.lean").read_bytes()
assert audit_source.count(addition) == 1 and audit_source.replace(addition, b"", 1) == original
assert audit_source.index(addition) < audit_source.index(b"/-!")
report = load("public-readback/prepend-grouping-full-readback.json")
printer = (evidence / (full_stem + ".source.lean")).read_bytes()
raw = (evidence / (full_stem + ".log")).read_bytes()
options = ["maxRecDepth 30000", "maxHeartbeats 0", "linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true",
    "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]
tail = "\n" + "".join("set_option " + option + "\n" for option in options)
for short, kind in specs:
    tail += "".join(d + namespace + short + "\n" for d in ["#check @", "#print ", "#print axioms "])
assert printer == source + tail.encode() and len(printer.splitlines()) == source_lines + 38 and len(tail.splitlines()) == 38
assert all(printer.decode().splitlines().count("set_option " + option) == 1 for option in options)
assert all(printer.decode().splitlines().count(d + namespace + short) == 1 for short, kind in specs for d in ["#check @", "#print ", "#print axioms "])
for stem, row in jobs.items():
    if row[1] and "public" in stem:
        public_source = (evidence / (stem + ".source.lean")).read_bytes()
        assert any(public_source == (evidence / path).read_bytes() + tail.encode() for path in variants), stem
assert source.rstrip().endswith(("end MicroCFTA." + name).encode())
assert (report["source_sha256"], report["source_lines"], report["printer_sha256"]) == (selected_sha, source_lines, digest(printer))
assert report["log_sha256"] == digest(raw) and report["log_bytes"] == len(raw) == int("133490")
assert report["receipt_sha256"] == digest((evidence / (full_stem + ".json")).read_bytes()) and report["owned_public_job_exit"] == 0
assert all(report[key] for key in ["all_eight_printer_settings", "exact_module_and_diagnostic_tail", "diagnostic_limits_after_module_only", "no_omissions"])
assert (report["pp_option_count"], report["linter_option_count"], report["diagnostic_limit_count"]) == (7, 1, 2)
assert report["configured_paths"] == {key: str(path.resolve()) for key, path in dict(source=evidence / (name + ".lean"), printer=evidence / (full_stem + ".source.lean"), raw=evidence / (full_stem + ".log"), receipt=evidence / (full_stem + ".json")).items()}
assert [(item["head"], item["kind"]) for item in report["heads"]] == [(namespace + short, kind) for short, kind in specs]
head_metrics = json.loads('{"insertWith": {"type_bytes": 204, "type_characters": 196, "type_logical_lines": 4, "type_line_feeds": 3, "type_final_newline": false, "type_sha256": "48d0904f048cbeafc8e95f8b22efc2393f403c1732296c487e69c9bde0e1c2be", "body_bytes": 582, "body_characters": 582, "body_sha256": "fb73df02427535a9abd16c026862f578506d250c49a2059ce44d511ea5c5d1f7", "actual_axioms": [], "printed_type_bytes": 204, "printed_type_sha256": "48d0904f048cbeafc8e95f8b22efc2393f403c1732296c487e69c9bde0e1c2be", "raw_type_byte_identity": true}, "fromRows": {"type_bytes": 139, "type_characters": 129, "type_logical_lines": 2, "type_line_feeds": 1, "type_final_newline": false, "type_sha256": "094eb0b94d3ffba52ac789f9f51dcbfa5a44f017b4b33e5cf5ac8e165512ae28", "body_bytes": 392, "body_characters": 392, "body_sha256": "f465ea3d8a75a6a6de9c892b2453bb4179447f0b57965dc49b74f25f1ee8e75f", "actual_axioms": [], "printed_type_bytes": 139, "printed_type_sha256": "094eb0b94d3ffba52ac789f9f51dcbfa5a44f017b4b33e5cf5ac8e165512ae28", "raw_type_byte_identity": true}, "reverseTable": {"type_bytes": 132, "type_characters": 128, "type_logical_lines": 2, "type_line_feeds": 1, "type_final_newline": false, "type_sha256": "1c8a53b41b8713b00c11021bc6eceb70ac44f344491d7d669fc0f57c9c914528", "body_bytes": 120, "body_characters": 120, "body_sha256": "d8be55376001290793be4df6a07d6667af2cef99bc6e51242d381c1f02b7d1c5", "actual_axioms": [], "printed_type_bytes": 132, "printed_type_sha256": "1c8a53b41b8713b00c11021bc6eceb70ac44f344491d7d669fc0f57c9c914528", "raw_type_byte_identity": true}, "pair_fold": {"type_bytes": 653, "type_characters": 649, "type_logical_lines": 8, "type_line_feeds": 7, "type_final_newline": false, "type_sha256": "9dc4d1e79df4da3e0ead7a744b916ab00c8352344aa090cbfe469a9a4988d800", "body_bytes": 5885, "body_characters": 5883, "body_sha256": "f1a608dd9a6862bff58da0507a17da32b01e8d5075ee8227376dad85124cf5de", "actual_axioms": ["propext"], "printed_type_bytes": 653, "printed_type_sha256": "80591714a25308241133eda0250a552e996f6531f7cbfa031bdf5338640d1061", "raw_type_byte_identity": false}, "reverse_insert_singleton": {"type_bytes": 698, "type_characters": 696, "type_logical_lines": 9, "type_line_feeds": 8, "type_final_newline": false, "type_sha256": "fd13a4e124d61c37b4c120aab3211187fbe18ab2f5c8a3a355340969daf69f05", "body_bytes": 44998, "body_characters": 44978, "body_sha256": "f9a017c442544dd26bdacd467e44f2c6fffcef0d0ba8f09b4a47b5daebe11816", "actual_axioms": ["Quot.sound", "propext"], "printed_type_bytes": 700, "printed_type_sha256": "2647b3b5bfd2290c719ba98df5e8537b7afeaf8756b68064ddd23336c092b2bb", "raw_type_byte_identity": false}, "reverse_fold": {"type_bytes": 984, "type_characters": 980, "type_logical_lines": 14, "type_line_feeds": 13, "type_final_newline": false, "type_sha256": "e7abc72eb5ae11313b0f756be9443ce3b225a81bf3eedd247face7aaa24db0d3", "body_bytes": 19092, "body_characters": 19090, "body_sha256": "1f4240edba3f9b093683c31faaf4fbf964e4ab76976d4d5c690181cb46d1d4dc", "actual_axioms": ["Quot.sound", "propext"], "printed_type_bytes": 984, "printed_type_sha256": "e7abc72eb5ae11313b0f756be9443ce3b225a81bf3eedd247face7aaa24db0d3", "raw_type_byte_identity": true}, "reverse_fromRows": {"type_bytes": 386, "type_characters": 382, "type_logical_lines": 6, "type_line_feeds": 5, "type_final_newline": false, "type_sha256": "3344b088d26e80b94b33956fa84b16cb6af5408602461acb91fda1a3d6b72a30", "body_bytes": 7590, "body_characters": 7590, "body_sha256": "c51017392dab076c72f069bd0190a31d04daa77f0670a0fdf73aea7fb2ea9e21", "actual_axioms": ["Quot.sound", "propext"], "printed_type_bytes": 386, "printed_type_sha256": "3344b088d26e80b94b33956fa84b16cb6af5408602461acb91fda1a3d6b72a30", "raw_type_byte_identity": true}, "iteration_reverse": {"type_bytes": 661, "type_characters": 657, "type_logical_lines": 10, "type_line_feeds": 9, "type_final_newline": false, "type_sha256": "15c4e831693315e33e19ee2140d5f757843e1d25833c40ca89f21a425e58a4b6", "body_bytes": 35373, "body_characters": 35347, "body_sha256": "f749fec09dcbb20718ae0b1f5263c70a05af6c15b67ee32e4687d29169b8c603", "actual_axioms": ["Quot.sound", "propext"], "printed_type_bytes": 661, "printed_type_sha256": "15c4e831693315e33e19ee2140d5f757843e1d25833c40ca89f21a425e58a4b6", "raw_type_byte_identity": true}, "iteration_permutation": {"type_bytes": 617, "type_characters": 611, "type_logical_lines": 9, "type_line_feeds": 8, "type_final_newline": false, "type_sha256": "8c2e931f0f424be14138db69cb52d15859f0cb4928faa4ba90abae6bca0175a9", "body_bytes": 8523, "body_characters": 8517, "body_sha256": "f3c94c43694135c2d52854dce337c735a0c3d00815d40a5482669e6e94111dbe", "actual_axioms": ["Classical.choice", "Quot.sound", "propext"], "printed_type_bytes": 617, "printed_type_sha256": "8c2e931f0f424be14138db69cb52d15859f0cb4928faa4ba90abae6bca0175a9", "raw_type_byte_identity": true}}')
assert list(head_metrics) == short_names
log = raw.decode()
assert not re.search(r"sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.", log)
starts = []
for short, kind in specs:
    pattern = re.escape(namespace + short) + r"(?:\.\{[^}\n]*\})?"
    matches = list(re.finditer(r"^(?:@)?" + pattern + r" :", log, re.M))
    assert len(matches) == 1, short
    starts.append(matches[0])
assert starts == sorted(starts, key=lambda match: match.start()) and not log[:starts[0].start()].strip()
allowed, actual_by_head, retained_names = {"Classical.choice", "Quot.sound", "propext"}, {}, []
for index, (short, kind) in enumerate(specs):
    head = namespace + short
    segment = log[starts[index].end():starts[index + 1].start() if index + 1 < len(starts) else len(log)]
    pattern = re.escape(head) + r"(?:\.\{[^}\n]*\})?"
    delimiters = list(re.finditer(r"\n" + kind + " " + pattern + r" :", segment))
    assert len(delimiters) == 1, short
    checked, printed = segment[:delimiters[0].start()], segment[delimiters[0].end():]
    axioms = list(re.finditer(r"^'" + re.escape(head) + r"' (depends on axioms:|does not depend on any axioms)", printed, re.M))
    assert len(axioms) == 1, short
    axiom = axioms[0]
    declaration, axiom_output = printed[:axiom.start()], printed[axiom.start():]
    normalized, matches = canonical(checked), []
    for match in re.finditer(r" :=\n", declaration):
        prefix = canonical(declaration[:match.start()])
        if prefix == normalized:
            matches.append(match)
        elif len(prefix) > len(normalized):
            break
    assert len(matches) == 1, short
    declared, body = declaration[:matches[0].start()], declaration[matches[0].end():]
    raw_identity = checked.encode() == declared.encode()
    assert canonical(checked) == canonical(declared)
    metric = head_metrics[short]
    assert set(metric) == {"type_bytes", "type_characters", "type_logical_lines", "type_line_feeds", "type_final_newline", "type_sha256", "body_bytes", "body_characters", "body_sha256", "actual_axioms", "printed_type_bytes", "printed_type_sha256", "raw_type_byte_identity"}
    assert len(checked) == metric["type_characters"] and len(checked.encode()) == metric["type_bytes"]
    assert len(checked.splitlines()) == metric["type_logical_lines"] and checked.count("\n") == metric["type_line_feeds"] and checked.endswith("\n") == metric["type_final_newline"]
    assert digest(checked.encode()) == metric["type_sha256"]
    assert len(declared.encode()) == metric["printed_type_bytes"] and digest(declared.encode()) == metric["printed_type_sha256"]
    assert raw_identity is metric["raw_type_byte_identity"]
    assert not any(token in checked + declared for token in ["_private", "✝", "†", "‡"])
    assert not any(re.search(re.escape(namespace + helper) + r"(?![\w'])", checked + declared) for helper in helpers)
    head_report = report["heads"][index]
    assert all(head_report[key] for key in ["check_print_type_identity", "check_print_type_lexical_identity", "unique_complete_type_body_delimiter", "actual_axioms_within_standard_allowed"])
    assert head_report["check_print_type_byte_identity"] is raw_identity
    assert head_report["private_namespace_helpers_checked"] == helpers and head_report["private_type_spellings_checked"] == ["_private", "✝", "†", "‡"] and head_report["private_public_type_names"] is False
    assert head_report["checked_type_characters"] == len(checked) and head_report["normalized_type_characters"] == len(normalized)
    assert head_report["checked_type_bytes"] == len(checked.encode()) and head_report["checked_type_sha256"] == digest(checked.encode())
    assert head_report["printed_type_bytes"] == len(declared.encode()) and head_report["printed_type_characters"] == len(declared)
    assert head_report["printed_type_sha256"] == digest(declared.encode()) and head_report["canonical_type_sha256"] == digest(normalized.encode())
    assert head_report["body_characters"] == len(body) == metric["body_characters"] and len(body.encode()) == metric["body_bytes"]
    assert body.startswith("fun ") and len(body) > 50 and digest(body.encode()) == metric["body_sha256"]
    values = re.fullmatch(r"\s*\[([^\]]*)\]\s*", printed[axiom.end():]) if axiom.group(1) == "depends on axioms:" else None
    assert values or (axiom.group(1) == "does not depend on any axioms" and not printed[axiom.end():].strip())
    actual_axioms = {re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in values.group(1).split(",") if item.strip()} if values else set()
    assert sorted(actual_axioms) == head_report["actual_axioms"] == metric["actual_axioms"] and actual_axioms <= allowed
    assert head_report["actual_standard_three_axioms"] == (actual_axioms == allowed)
    actual_by_head[short] = sorted(actual_axioms)
    for suffix, text in [("public-type", checked), ("printed-public-type", declared), ("body", body), ("axioms", axiom_output)]:
        filename = "prepend-grouping-" + short + "-" + suffix + ".txt"
        retained = (evidence / "public-readback" / filename).read_bytes()
        assert retained == text.encode() and report["retained_slices"][filename] == dict(bytes=len(retained), sha256=digest(retained))
        retained_names.append(filename)
assert set(report["retained_slices"]) == set(retained_names)
assert digest((evidence / "full-preparation-v2/check-full-public.py").read_bytes()) == "3f88ecfe2662cc630dc73caee5c3862970f51e405344e2d6e14f29c82de9459e"
assert digest((evidence / "check-full-public-v2.py").read_bytes()) == "3f88ecfe2662cc630dc73caee5c3862970f51e405344e2d6e14f29c82de9459e"
review = load("root-full-review.json")
assert review["status"] == "ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT" and review["source_sha256"] == selected_sha and review["source_lines"] == source_lines
assert review["public_heads"] == [namespace + short for short in short_names]
assert review["complete_public_type_root_review"] == review["independent_complete_public_type_review"] == "CLEAR"
assert review["root_read_complete_public_types"] and review["root_printed_type_lexical_identity_verified"] and review["four_private_markers_and_all_helpers_absent_from_type"]
assert review["raw_type_byte_identity_by_head"] == {short: head_metrics[short]["raw_type_byte_identity"] for short in short_names}
assert all(review.get(key, all(head_metrics[short]["raw_type_byte_identity"] for short in short_names)) == all(head_metrics[short]["raw_type_byte_identity"] for short in short_names) for key in ["root_printed_type_byte_identity_verified", "check_print_type_byte_identity"])
assert review["types_sha256"] == {short: head_metrics[short]["type_sha256"] for short in short_names}
assert review["full_raw_sha256"] == digest(raw) and review["actual_axioms_by_head"] == actual_by_head
assert review["body_retained_and_programmatically_checked"] and review["whole_body_manual_read_claimed"] is False
required_true = ['pure_prepend_bucket_reversal_bridge', 'literal_new_before_old_combination', 'none_and_some_empty_distinct', 'arbitrary_initial_table_reversal', 'duplicate_occurrences_retained', 'exact_iteration_keys_and_order_retained', 'reversed_buckets_permute_canonical_groups', 'all_nine_public_declarations_reviewed', 'definition_equations_source_review_clear', 'definitions_and_theorem_headers_exact', 'no_private_declarations']
required_false = ['hash_map_refinement_claimed', 'haskell_execution_or_refinement_claimed', 'stateful_group_traversal_claimed', 'group_execution_or_capacity_producer_claimed', 'public_pass_claimed', 'whole_goal_complete', 'heap_or_node_identity_claimed', 'fixed_hash_map_outer_key_order_claimed', 'generated_parent_or_mu_claimed', 'practical_width_or_convergence_claimed', 'future_success_or_semantic_oracle', 'changes_to_previous_grouping_modules_claimed']
assert all(review[key] is True for key in required_true) and all(review[key] is False for key in required_false)
audit = (evidence / (audit_stem + ".log")).read_text()
build = re.search(r"Build completed successfully \((\d+) jobs\)\.", audit)
dependencies = re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", audit)
assert build and dependencies and not re.search(r"\berror(?:\([^)]*\))?:", audit)
assert int(build.group(1)) == int("3638") and int(dependencies.group(1)) == int("75494")
print(json.dumps(dict(status="PASS", live=args.live, **metrics, new_lean_lake_jobs=0, selected_modules=1, original_archives=1,
    public_definitions=3, public_theorems=6, audit_build_jobs=int(build.group(1)), audit_dependencies=int(dependencies.group(1)), audit_log_sha256=digest(audit.encode())), indent=2))
