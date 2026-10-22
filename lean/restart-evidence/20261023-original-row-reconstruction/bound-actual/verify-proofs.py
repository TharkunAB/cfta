"""Check saved original-row-reconstruction evidence. This script does not run Lean."""
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
evidence = root / "lean/restart-evidence/20261023-original-row-reconstruction"
def load(name):
    return json.loads((evidence / name).read_text())
def digest(data):
    return hashlib.sha256(data).hexdigest()
def canonical(text):
    return re.sub(r"[ \t\r\n]+", " ", text).strip(" \t\r\n")
name = "SourceCurrentOriginalRowReconstruction"
namespace = "MicroCFTA." + name + "."
specs = json.loads('[["ordinary_complete", "theorem"]]')
short_names = [short for short, kind in specs]
selected_sha = "69ed5b8d01f7bcd1d21aa4a66206c9f0bc9480c728c695bfafd7e8222621e435"
source_lines = int("210")
strict_stem, full_stem, audit_stem = "original-row-reconstruction-strict-2", "original-row-reconstruction-public-1", "original-row-reconstruction-audit-1"
metrics = dict(actual_jobs=int("4"), source_jobs=int("3"), audit_jobs=int("1"),
    failed_jobs=int("1"), warned_source_exit_zero_jobs=int("0"),
    rejected_public_type_jobs=int("0"))
jobs = json.loads('{"original-row-reconstruction-audit-1": [0, null, "f97a5d4ff4987b5276453d67d2c9560aea9de81b315a2a9510ea4165fafa32c9", 0, 0], "original-row-reconstruction-public-1": [0, "9832d30fdb8c73fd65aff29a6017096b5b03561859ea1117bd332ff5da27c99f", "6b234343f2185f8a9c889ef4c165d8298024155a30b40da0e9f83336080a94a3", 0, 0], "original-row-reconstruction-strict-1": [1, "31f617cdb892cf7eff50ea6f2aa671cb590b94211615e798bddad90538637276", "9e4eab7f245e7c14e149222ca0473e02a6faab6b2e73bb1a2797d3963189e0fa", 2, 0], "original-row-reconstruction-strict-2": [0, "69ed5b8d01f7bcd1d21aa4a66206c9f0bc9480c728c695bfafd7e8222621e435", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", 0, 0]}')
rejected = json.loads('[]')
assert re.fullmatch(r"[0-9a-f]{64}", selected_sha)
assert jobs and all(stem.startswith("original-row-reconstruction-") for stem in jobs)
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
assert len(strict_source.splitlines()) == source_lines <= int("350")
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
assert history == json.loads('{"status": "ROOT_ACCEPTED", "selected_source_sha256": "69ed5b8d01f7bcd1d21aa4a66206c9f0bc9480c728c695bfafd7e8222621e435", "variants": [{"path": "proposal/drafts/SourceCurrentOriginalRowReconstruction.initial210.lean.txt", "sha256": "14b4fb885003690913e63aa390e65de43f6ba624480b647e8d144836828bb783", "lines": 210, "reason": "Initial complete uncompiled source. Two preflight argument/name precautions precede the first actual strict input."}, {"path": "proposal/SourceCurrentOriginalRowReconstruction.lean", "sha256": "31f617cdb892cf7eff50ea6f2aa671cb590b94211615e798bddad90538637276", "lines": 210, "reason": "First submitted complete source. Actual strict1 exited 1 with exactly two record-field parse errors and no warnings."}, {"path": "syntax-repair-1/SourceCurrentOriginalRowReconstruction.lean", "sha256": "69ed5b8d01f7bcd1d21aa4a66206c9f0bc9480c728c695bfafd7e8222621e435", "lines": 210, "reason": "Syntax-only three-application parenthesis repair. Actual strict2 is clean and sole FULL1 has accepted saved reader metadata."}], "artifacts": [{"path": "actual-header.lean.txt", "bytes": 6259, "sha256": "114548bcd08ccae269f35300e8a03ccd2a933c11797890db25b073b5138fd8c5"}, {"path": "original-row-reconstruction-public-1.json", "bytes": 838, "sha256": "1a61b2ca4e5192ca1793b874b318b9bab561e43bc69232bd30a981e78913e656"}, {"path": "original-row-reconstruction-public-1.limits.json", "bytes": 90, "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"path": "original-row-reconstruction-public-1.log", "bytes": 15757750, "sha256": "6b234343f2185f8a9c889ef4c165d8298024155a30b40da0e9f83336080a94a3"}, {"path": "original-row-reconstruction-public-1.source.lean", "bytes": 13831, "sha256": "9832d30fdb8c73fd65aff29a6017096b5b03561859ea1117bd332ff5da27c99f"}, {"path": "original-row-reconstruction-public-1.usage.json", "bytes": 114, "sha256": "84b1696b73e85ab834b674c09a2d87059a08cfeb2ea034923dc5346634e3420b"}, {"path": "original-row-reconstruction-strict-1.json", "bytes": 838, "sha256": "9238a1d0aa2fd5f0291c236c0ad6893cf1ff9583bc899eedde4b84ff908943c5"}, {"path": "original-row-reconstruction-strict-1.limits.json", "bytes": 90, "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"path": "original-row-reconstruction-strict-1.log", "bytes": 364, "sha256": "9e4eab7f245e7c14e149222ca0473e02a6faab6b2e73bb1a2797d3963189e0fa"}, {"path": "original-row-reconstruction-strict-1.source.lean", "bytes": 13303, "sha256": "31f617cdb892cf7eff50ea6f2aa671cb590b94211615e798bddad90538637276"}, {"path": "original-row-reconstruction-strict-1.usage.json", "bytes": 114, "sha256": "db805ad3f60c56c4d44c2d57529f68a439d895d51c8d84638b9c079b1ad8953e"}, {"path": "original-row-reconstruction-strict-2.json", "bytes": 838, "sha256": "18a562f50277eafc82c6d0be35c691ac8b14286dfabf3d47d771fb220f25f309"}, {"path": "original-row-reconstruction-strict-2.limits.json", "bytes": 90, "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"path": "original-row-reconstruction-strict-2.log", "bytes": 0, "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"}, {"path": "original-row-reconstruction-strict-2.source.lean", "bytes": 13309, "sha256": "69ed5b8d01f7bcd1d21aa4a66206c9f0bc9480c728c695bfafd7e8222621e435"}, {"path": "original-row-reconstruction-strict-2.usage.json", "bytes": 114, "sha256": "d449a5d372932021fc1900be44aa1473726bdfee3ce746820f06f329c3bdfc21"}, {"path": "proposal/FROZEN.json", "bytes": 657, "sha256": "c57cf2ab2e58401331a96647005de0e0711ce47963d585c62481814b5b6ba07b"}, {"path": "proposal/bodyless-declarations.lean.txt", "bytes": 8070, "sha256": "62536adae238d3f187108cb22f750cb57bac4cbbd67df8e2ceedda5855259bf1"}, {"path": "proposal/note.md", "bytes": 1158, "sha256": "256df9de0507d3f9badff5d093d6f288366c86559ca00c3a333fefaf785257c1"}, {"path": "proposal/packaging-static-diagnostic.md", "bytes": 420, "sha256": "6a1292843b2d73518055771a5a5e092f9aa2b34521a6b71026b4e0e979012e85"}, {"path": "proposal/pins.json", "bytes": 21427, "sha256": "77a0d9ac6cb148e2ab20e507c707ed9ac6619d47f045331b39b0998023a3eb61"}, {"path": "proposal/preflight-body-arguments.patch", "bytes": 688, "sha256": "cb017ed2ec251de0af33a59f36b8853f25ae898a9818e48c5423aea11ca7c5bc"}, {"path": "proposal/preflight.json", "bytes": 1211, "sha256": "9447aa17108611120e6dcf77feee9acdc05de7752d182b13951b800d4620f123"}, {"path": "proposal/scope-status.json", "bytes": 509, "sha256": "e28acd2152cabea5713681300dbfcc30e9ea5c1a36f747f5d85cf35c3963e9ff"}, {"path": "proposal/source-addition.patch", "bytes": 6285, "sha256": "44018ec3b9d83a5417e138ef823cb1bd079754a6b53cd9a2e97ad73162d9c93f"}, {"path": "public-readback/original-row-reconstruction-full-readback.json", "bytes": 3389, "sha256": "2c847d986adaea974eef1da8fdb80f011ba541eb90ced366d663726f21fb9a97"}, {"path": "public-readback/original-row-reconstruction-ordinary_complete-axioms.txt", "bytes": 138, "sha256": "f9757bd4ce02955c8498b14bc1a075d9d60660833134e2037e0619074e8ea48e"}, {"path": "public-readback/original-row-reconstruction-ordinary_complete-body.txt", "bytes": 15353860, "sha256": "3c8ff79e201af49fa64370b6925b0a40f4485ddcd8396859d862a7481f0ff274"}, {"path": "public-readback/original-row-reconstruction-ordinary_complete-printed-public-type.txt", "bytes": 201801, "sha256": "41b97f6d0dc108847e84ef67e0011a880bc222ec1849513161649bb2a031e5bb"}, {"path": "public-readback/original-row-reconstruction-ordinary_complete-public-type.txt", "bytes": 201801, "sha256": "41b97f6d0dc108847e84ef67e0011a880bc222ec1849513161649bb2a031e5bb"}, {"path": "root-declaration-review.before-syntax-repair.json", "bytes": 1603, "sha256": "75cc712dd39863ac237d86b66f7d231d0d446efefed36bb1b3b2837749f9e750"}, {"path": "root-declaration-review.json", "bytes": 1850, "sha256": "519477fca46fe01fb038543707a3ce875fc366676b363cc36da99c5ac22a0e17"}, {"path": "root-full-tools-review.before-signature-path-repair.json", "bytes": 1584, "sha256": "ddba0235e718d81b1782bb6341580f03d362f012ccec7825fd7ff4dac5676916"}, {"path": "root-full-tools-review.json", "bytes": 1831, "sha256": "050a2708ea4491c2873acc09e24e566e50b74058ab9f5c4b72b6ad6f3ea9de48"}, {"path": "root-source-compile-gate-repair-1.json", "bytes": 797, "sha256": "3f865bbe7e6312fb95aee7aac2fb1d4ebef529745a3bf47fc22c734aeeba9c72"}, {"path": "root-source-compile-gate.json", "bytes": 728, "sha256": "2f6fe7c1ed102f65f05bce3a674fe47ba9f3bd3e9af5e5af4077c7b19c6a6107"}, {"path": "root-source-review.json", "bytes": 359, "sha256": "49630bfe2683658b5e7a43d2c3f5a54b813055769c30a6457bf8cdde40d31611"}, {"path": "selected-source-gate.json", "bytes": 278, "sha256": "37a6b728322beecad15433a44ce9dd132308e3f5657f837103d932786bca186a"}, {"path": "selected-sources.json", "bytes": 279, "sha256": "572c0ce013117b789783a6149fc9f377f9ff07f1684d84454847d354c76a5a35"}, {"path": "signature-path-audit/FROZEN.json", "bytes": 357, "sha256": "05cd1c44e2f1708cad6388b7e080822213aeadcdc0458688c1b07a1418aac741"}, {"path": "signature-path-audit/pins.json", "bytes": 2701, "sha256": "0079fadf94c14e1cf3932c3c46b94ee297ddedbe6b7749cb015bdb58e69985ed"}, {"path": "signature-path-audit/review.md", "bytes": 1773, "sha256": "ffa36d2d489775af23f796c8518d2ba0a3a24c6a11380ab30b85f4ffb6646bd0"}, {"path": "signature-path-audit/reviewed-overlay/FROZEN.json", "bytes": 524, "sha256": "f95e45d150eec1aaefa643e1d0c3bf7be831cbf6693c9861899ac5b28534948c"}, {"path": "signature-path-audit/reviewed-overlay/diffs/prepare-selected-full.py.patch", "bytes": 777, "sha256": "5d61eb454e1bf73aa91f6c80f7734891ec6404054852641f7989b5d8e6da9313"}, {"path": "signature-path-audit/reviewed-overlay/diffs/verify-proofs.py.patch", "bytes": 859, "sha256": "047884a1236809fdf72acc7929094b7641b3a067bfe7f32d39907f4b2cf3123f"}, {"path": "signature-path-audit/reviewed-overlay/future-contract-path-binding.json", "bytes": 731, "sha256": "ffc4f6e8ef314c05213d46678eb0f4dc5a89c41674c81038cc5529543179be8c"}, {"path": "signature-path-audit/reviewed-overlay/note.md", "bytes": 1060, "sha256": "961fee547706c9605da49b3a53cda761627047861c2f71705a45af2bcd04b537"}, {"path": "signature-path-audit/reviewed-overlay/pins.json", "bytes": 1513, "sha256": "dd9260a1cda7c633adf1a793036c0d6d68cd4f94437cfb1df61b556c3f50a054"}, {"path": "signature-path-audit/reviewed-overlay/predecessors/prepare-selected-full.py", "bytes": 3680, "sha256": "c7e73ee77735fe40b40d99836f72b09af2862410f51e7679df68d57c32b30844"}, {"path": "signature-path-audit/reviewed-overlay/predecessors/verify-proofs.py", "bytes": 23351, "sha256": "2bf1df9b5bd04fc2a08a0e5610cc9b7b83dd0cb195d76b4c3027fdd843c040b4"}, {"path": "signature-path-audit/reviewed-overlay/prepare-selected-full.py", "bytes": 3684, "sha256": "8c3398646b2f8e982a0cbc17167d06133628d4d23f96f040e1b4019bd831a58c"}, {"path": "signature-path-audit/reviewed-overlay/static-comparison.json", "bytes": 1239, "sha256": "f004ce86742b26854da3216a973ba072a47f78f176f1990267baec90c2ad3f86"}, {"path": "signature-path-audit/reviewed-overlay/unchanged-full-components.json", "bytes": 722, "sha256": "c7bc196bafcd9c1c519c106233f54e838723edae8a20d76e1f23f975b829b601"}, {"path": "signature-path-audit/reviewed-overlay/verify-proofs.py", "bytes": 23353, "sha256": "d06a34a1fb095e5aaf35d450961c107da25ea4b5ec000d5d45bd27e1968519d6"}, {"path": "signature-path-audit/reviewer-diagnostic.json", "bytes": 519, "sha256": "fbec59f8ce3b9ed94600c8d403c630d0e856c10b2531c0915568b2d9ee7598d5"}, {"path": "signature-path-audit/static-review-results.json", "bytes": 2152, "sha256": "91ee7c50af4b5be9faf97405b3926343b7de789cf3feaf07336c61d02417bc6a"}, {"path": "signature-path-audit/unchanged-components/check-full-public.py", "bytes": 8344, "sha256": "fd026aa62c8cf9f663f7a9066a66d1ea1021d0b88b980cebb7aa49dd0e94a3c7"}, {"path": "signature-path-audit/unchanged-components/diagnostic-tail.lean.txt", "bytes": 522, "sha256": "57d1636e639847d2494e18fb83eb9a6b606b50610e62c50585854a95a8190f5d"}, {"path": "signature-path-audit/unchanged-components/root-run-check.py", "bytes": 1971, "sha256": "37784c72c779cac7e5cbd2bfdbfaf10bf90a1cda37c117debe04495b74d604ff"}, {"path": "signature-path-repair/FROZEN.json", "bytes": 524, "sha256": "f95e45d150eec1aaefa643e1d0c3bf7be831cbf6693c9861899ac5b28534948c"}, {"path": "signature-path-repair/diffs/prepare-selected-full.py.patch", "bytes": 777, "sha256": "5d61eb454e1bf73aa91f6c80f7734891ec6404054852641f7989b5d8e6da9313"}, {"path": "signature-path-repair/diffs/verify-proofs.py.patch", "bytes": 859, "sha256": "047884a1236809fdf72acc7929094b7641b3a067bfe7f32d39907f4b2cf3123f"}, {"path": "signature-path-repair/future-contract-path-binding.json", "bytes": 731, "sha256": "ffc4f6e8ef314c05213d46678eb0f4dc5a89c41674c81038cc5529543179be8c"}, {"path": "signature-path-repair/note.md", "bytes": 1060, "sha256": "961fee547706c9605da49b3a53cda761627047861c2f71705a45af2bcd04b537"}, {"path": "signature-path-repair/pins.json", "bytes": 1513, "sha256": "dd9260a1cda7c633adf1a793036c0d6d68cd4f94437cfb1df61b556c3f50a054"}, {"path": "signature-path-repair/predecessors/prepare-selected-full.py", "bytes": 3680, "sha256": "c7e73ee77735fe40b40d99836f72b09af2862410f51e7679df68d57c32b30844"}, {"path": "signature-path-repair/predecessors/verify-proofs.py", "bytes": 23351, "sha256": "2bf1df9b5bd04fc2a08a0e5610cc9b7b83dd0cb195d76b4c3027fdd843c040b4"}, {"path": "signature-path-repair/prepare-selected-full.py", "bytes": 3684, "sha256": "8c3398646b2f8e982a0cbc17167d06133628d4d23f96f040e1b4019bd831a58c"}, {"path": "signature-path-repair/static-comparison.json", "bytes": 1239, "sha256": "f004ce86742b26854da3216a973ba072a47f78f176f1990267baec90c2ad3f86"}, {"path": "signature-path-repair/unchanged-full-components.json", "bytes": 722, "sha256": "c7bc196bafcd9c1c519c106233f54e838723edae8a20d76e1f23f975b829b601"}, {"path": "signature-path-repair/verify-proofs.py", "bytes": 23353, "sha256": "d06a34a1fb095e5aaf35d450961c107da25ea4b5ec000d5d45bd27e1968519d6"}, {"path": "signature-plan/context.lean.txt", "bytes": 988, "sha256": "11cd9fae21adc0ac9dec284c42c466f6c335dbcb6b682d82cb9277531719923e"}, {"path": "signature-plan/contracts.json", "bytes": 683, "sha256": "c2202a31a91d7df7b2440a88bd3c2654f7929d7d2d668635c02fc501625d5f04"}, {"path": "signature-plan/local-statements.lean.txt", "bytes": 916, "sha256": "81ccd69cff8e44db1aa179513744ed6cbda3f6d1bcc3e816edf82a812a363d48"}, {"path": "signature-plan/private-header.lean.txt", "bytes": 775, "sha256": "d607d758b69efca49985e62e9fddac239edce2a9bbf48392c81603af07acc241"}, {"path": "signature-plan/public-header.lean.txt", "bytes": 6251, "sha256": "a233a223b51de65d2d70e17caeeeff06289fb2ad296b3b46e2856ac509aa23d2"}, {"path": "signature-repair/context.lean.txt", "bytes": 988, "sha256": "11cd9fae21adc0ac9dec284c42c466f6c335dbcb6b682d82cb9277531719923e"}, {"path": "signature-repair/contracts.json", "bytes": 683, "sha256": "63d356619295a39168f5bc4011bfbabb6df6666784ee476fc0313582973f6a4f"}, {"path": "signature-repair/local-statements.lean.txt", "bytes": 916, "sha256": "81ccd69cff8e44db1aa179513744ed6cbda3f6d1bcc3e816edf82a812a363d48"}, {"path": "signature-repair/private-header.lean.txt", "bytes": 777, "sha256": "7642de428d408cf86ee2d900ea7f49f0fe956824b5548118b64cbfa113c198a9"}, {"path": "signature-repair/public-header.lean.txt", "bytes": 6253, "sha256": "8ad6f9af84fa67b47e3e8295a470b4e04be07230809dfc694df004297b8444f4"}, {"path": "strict-1-failure-summary.json", "bytes": 577, "sha256": "6875a3de78c745149e2c1af34bce430423e37fff959a0455bbe8933231264c45"}, {"path": "syntax-repair-1/FROZEN.json", "bytes": 577, "sha256": "674993d001b297186ad5a58f1eb682f6b0f573c203e952006473f4cc9ac11cc0"}, {"path": "syntax-repair-1/note.md", "bytes": 1047, "sha256": "d62fba153b7a9f8b2d2f48d186ed12ad6dcdc77d7fa362d5bf9d3f9f5a7ba7f5"}, {"path": "syntax-repair-1/pins.json", "bytes": 20581, "sha256": "1ff693e8ef12e5eb4cebbfebf3656dd7d9034ebfc200ba34e8b853db947910cd"}, {"path": "syntax-repair-1/preflight.json", "bytes": 1054, "sha256": "cf95bc9bba4a74f630c0ccff7068f35068f6d436ecfcb3c4a158dfe3932768d4"}, {"path": "syntax-repair-1/private-header.lean.txt.patch", "bytes": 634, "sha256": "97a7d93d434fd5d8337a0857f9e8572cfb6949f830ad0b53fece297f638a074e"}, {"path": "syntax-repair-1/public-header.lean.txt.patch", "bytes": 756, "sha256": "f09287bd0d4dd618ff7efbf61685dd2f481f3457c7e83b349eb2d2b5be36c6a3"}, {"path": "syntax-repair-1/source-repair.patch", "bytes": 2098, "sha256": "3bac748386b4ac7f75ffb0d748353595da1b81dd43a8f051feb5bf6e69b6e34a"}, {"path": "original-row-reconstruction-audit-1.json", "bytes": 610, "sha256": "3574b292aedebb87be199760a5f56714e9b46ce447fd7f17ed114c1eccb3604f"}, {"path": "original-row-reconstruction-audit-1.log", "bytes": 695, "sha256": "f97a5d4ff4987b5276453d67d2c9560aea9de81b315a2a9510ea4165fafa32c9"}, {"path": "original-row-reconstruction-audit-1.limits.json", "bytes": 90, "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"path": "original-row-reconstruction-audit-1.usage.json", "bytes": 114, "sha256": "2b30b11503a8b4f0d82c0e93ad489a1609ea8e1b5f5e7cc35490c7c479ef5180"}], "patches": [{"before": "proposal/drafts/SourceCurrentOriginalRowReconstruction.initial210.lean.txt", "after": "proposal/SourceCurrentOriginalRowReconstruction.lean", "path": "proposal/preflight-body-arguments.patch", "sha256": "cb017ed2ec251de0af33a59f36b8853f25ae898a9818e48c5423aea11ca7c5bc", "fromfile": "drafts/SourceCurrentOriginalRowReconstruction.initial210.lean.txt", "tofile": "SourceCurrentOriginalRowReconstruction.lean", "reason": "Two uncompiled preflight precautions: mark the unused destructured request name and pass the returned result explicitly to edge_grows."}, {"before": "proposal/SourceCurrentOriginalRowReconstruction.lean", "after": "syntax-repair-1/SourceCurrentOriginalRowReconstruction.lean", "path": "syntax-repair-1/source-repair.patch", "sha256": "3bac748386b4ac7f75ffb0d748353595da1b81dd43a8f051feb5bf6e69b6e34a", "fromfile": "previous-source.lean.txt", "tofile": "SourceCurrentOriginalRowReconstruction.lean", "reason": "After actual strict1 two parse errors, add parentheses around the same multiline native advance application in private header, public header, and body."}], "rejected_public_types": []}') and history["status"] == "ROOT_ACCEPTED"
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
        assert 0 < len(data.splitlines()) == item["lines"] <= int("350") and isinstance(item["reason"], str) and item["reason"].strip()
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
contracts = json.loads('{"context.lean.txt": {"path": "signature-repair/context.lean.txt", "lines": 15, "sha256": "11cd9fae21adc0ac9dec284c42c466f6c335dbcb6b682d82cb9277531719923e"}, "private-header.lean.txt": {"path": "signature-repair/private-header.lean.txt", "lines": 12, "sha256": "7642de428d408cf86ee2d900ea7f49f0fe956824b5548118b64cbfa113c198a9"}, "public-header.lean.txt": {"path": "signature-repair/public-header.lean.txt", "lines": 97, "sha256": "8ad6f9af84fa67b47e3e8295a470b4e04be07230809dfc694df004297b8444f4"}, "local-statements.lean.txt": {"path": "signature-repair/local-statements.lean.txt", "lines": 13, "sha256": "81ccd69cff8e44db1aa179513744ed6cbda3f6d1bcc3e816edf82a812a363d48"}}')
expected_contracts = json.loads('{"context.lean.txt": {"path": "signature-repair/context.lean.txt", "lines": 15, "sha256": "11cd9fae21adc0ac9dec284c42c466f6c335dbcb6b682d82cb9277531719923e"}, "private-header.lean.txt": {"path": "signature-repair/private-header.lean.txt", "lines": 12, "sha256": "7642de428d408cf86ee2d900ea7f49f0fe956824b5548118b64cbfa113c198a9"}, "public-header.lean.txt": {"path": "signature-repair/public-header.lean.txt", "lines": 97, "sha256": "8ad6f9af84fa67b47e3e8295a470b4e04be07230809dfc694df004297b8444f4"}, "local-statements.lean.txt": {"path": "signature-repair/local-statements.lean.txt", "lines": 13, "sha256": "81ccd69cff8e44db1aa179513744ed6cbda3f6d1bcc3e816edf82a812a363d48"}}')
assert contracts == expected_contracts and list(contracts) == list(expected_contracts)
contract_data = {}
for filename, item in contracts.items():
    relative = Path(item["path"])
    assert not relative.is_absolute() and ".." not in relative.parts
    data = (evidence / relative).read_bytes()
    assert digest(data) == item["sha256"] and len(data.splitlines()) == item["lines"]
    contract_data[filename] = data
context = contract_data["context.lean.txt"]
assert source.startswith(context)
positions = []
assert list(contracts) == ["context.lean.txt", "private-header.lean.txt", "public-header.lean.txt", "local-statements.lean.txt"]
for filename in ["private-header.lean.txt", "public-header.lean.txt"]:
    header = contract_data[filename].rstrip(b"\n") + b" := by\n"
    assert source.count(header) == 1 and source.index(header) >= len(context), filename
    positions.append(source.index(header))
assert positions == sorted(set(positions))
local_types = contract_data["local-statements.lean.txt"].decode()
local_markers = list(re.finditer(r"(?m)^have ([A-Za-z_][A-Za-z_0-9']*)\b", local_types))
local_names = ["parentClosed", "residentRows", "closedRows", "rebuilt", "rebuiltSemantic", "rebuildExtension", "rebuiltGood", "rawDone"]
assert [match.group(1) for match in local_markers] == local_names
comments = local_types[:local_markers[0].start()].splitlines()
assert len(comments) == 2 and all(line.startswith("--") for line in comments)
public_header = contract_data["public-header.lean.txt"].rstrip(b"\n") + b" := by\n"
body_start = source.index(public_header) + len(public_header)
body_end = source.rfind(("\nend MicroCFTA." + name).encode())
assert body_start < body_end
public_body = source[body_start:body_end].decode()
local_positions = []
for index, marker in enumerate(local_markers):
    end = local_markers[index + 1].start() if index + 1 < len(local_markers) else len(local_types)
    fragment = local_types[marker.start():end].rstrip("\n") + " := by\n"
    assert public_body.count(fragment) == 1, marker.group(1)
    local_positions.append(public_body.index(fragment))
assert local_positions == sorted(set(local_positions))
public = re.findall(r"(?m)^\s*(?:(?:noncomputable|unsafe|partial)\s+)?(def|theorem|lemma|abbrev|opaque|instance|structure|inductive)\s+([^\s(\[{:=]+)", source.decode())
assert public == [(kind, short) for short, kind in specs]
helpers = []
for line in source.decode().splitlines():
    if re.match(r"^\s*(?:(?:noncomputable|unsafe|partial)\s+)?private\b", line):
        declaration = re.match(r"^\s*(?:(?:noncomputable|unsafe|partial)\s+)?private\s+(?:(?:noncomputable|unsafe|partial)\s+)?(?:def|theorem|lemma|abbrev|opaque|instance|structure|inductive)\s+([^\s(\[{:=]+)", line)
        assert declaration, ("unsupported private declaration", line)
        helpers.append(declaration.group(1))
assert helpers == json.loads('["stable_heap"]'), "Only the approved H23 private helpers are permitted"
declaration_review = load("root-declaration-review.json")
assert declaration_review["status"] == "ROOT_DECLARATION_REVIEW_CLEAR"
assert declaration_review["module"] == "MicroCFTA." + name
assert declaration_review["public_names"] == short_names and declaration_review["private_names"] == helpers
assert declaration_review.get("local_induction") == json.loads('null')
assert declaration_review["source_hard_stop"] == int("350")
assert declaration_review["contract_sha256"] == "63d356619295a39168f5bc4011bfbabb6df6666784ee476fc0313582973f6a4f"
assert digest((evidence / "signature-repair/contracts.json").read_bytes()) == declaration_review["contract_sha256"]
assert [{key: item[key] for key in ["path", "lines", "sha256"]} for item in declaration_review["contracts"]] == [dict(path=filename, lines=item["lines"], sha256=item["sha256"]) for filename, item in expected_contracts.items()]
if args.live:
    assert (root / source_path).read_bytes() == source
original = (evidence / "original-sources/Audit.original.lean.txt").read_bytes()
assert digest(original) == "ebcc4770268c142e8fb5370dadcbf9be224276f4c7b0240c9876df55444715de" and len(original.splitlines()) == 3128
assert load("original-source-index.json")["sources"] == [dict(path="lean/MicroCFTA/Audit.lean", snapshot="original-sources/Audit.original.lean.txt", lines=3128, sha256=digest(original))]
addition = b"import MicroCFTA.SourceCurrentOriginalRowReconstruction\n"
audit_source = (root / "lean/MicroCFTA/Audit.lean").read_bytes()
assert audit_source.count(addition) == 1 and audit_source.replace(addition, b"", 1) == original
assert audit_source.index(addition) < audit_source.index(b"/-!")
report = load("public-readback/original-row-reconstruction-full-readback.json")
printer = (evidence / (full_stem + ".source.lean")).read_bytes()
raw = (evidence / (full_stem + ".log")).read_bytes()
options = ["maxRecDepth 30000", "maxHeartbeats 0", "linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true",
    "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]
tail = "\n" + "".join("set_option " + option + "\n" for option in options)
for short, kind in specs:
    tail += "".join(d + namespace + short + "\n" for d in ["#check @", "#print ", "#print axioms "])
assert printer == source + tail.encode() and len(printer.splitlines()) == source_lines + 14 and len(tail.splitlines()) == 14
assert all(printer.decode().splitlines().count("set_option " + option) == 1 for option in options)
assert all(printer.decode().splitlines().count(d + namespace + short) == 1 for short, kind in specs for d in ["#check @", "#print ", "#print axioms "])
for stem, row in jobs.items():
    if row[1] and "public" in stem:
        public_source = (evidence / (stem + ".source.lean")).read_bytes()
        assert any(public_source == (evidence / path).read_bytes() + tail.encode() for path in variants), stem
assert source.rstrip().endswith(("end MicroCFTA." + name).encode())
assert (report["source_sha256"], report["source_lines"], report["printer_sha256"]) == (selected_sha, source_lines, digest(printer))
assert report["log_sha256"] == digest(raw) and report["log_bytes"] == len(raw) == int("15757750")
assert report["receipt_sha256"] == digest((evidence / (full_stem + ".json")).read_bytes()) and report["owned_public_job_exit"] == 0
assert all(report[key] for key in ["all_eight_printer_settings", "exact_module_and_diagnostic_tail", "diagnostic_limits_after_module_only", "no_omissions"])
assert (report["pp_option_count"], report["linter_option_count"], report["diagnostic_limit_count"]) == (7, 1, 2)
assert report["configured_paths"] == {key: str(path.resolve()) for key, path in dict(source=evidence / (name + ".lean"), printer=evidence / (full_stem + ".source.lean"), raw=evidence / (full_stem + ".log"), receipt=evidence / (full_stem + ".json")).items()}
assert [(item["head"], item["kind"]) for item in report["heads"]] == [(namespace + short, kind) for short, kind in specs]
head_metrics = json.loads('{"ordinary_complete": {"type_bytes": 201801, "type_characters": 201741, "type_logical_lines": 1951, "type_line_feeds": 1950, "type_final_newline": false, "type_sha256": "41b97f6d0dc108847e84ef67e0011a880bc222ec1849513161649bb2a031e5bb", "body_bytes": 15353860, "body_characters": 15353156, "body_sha256": "3c8ff79e201af49fa64370b6925b0a40f4485ddcd8396859d862a7481f0ff274", "actual_axioms": ["Classical.choice", "Quot.sound", "propext"], "printed_type_bytes": 201801, "printed_type_sha256": "41b97f6d0dc108847e84ef67e0011a880bc222ec1849513161649bb2a031e5bb", "raw_type_byte_identity": true}}')
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
        filename = "original-row-reconstruction-" + short + "-" + suffix + ".txt"
        retained = (evidence / "public-readback" / filename).read_bytes()
        assert retained == text.encode() and report["retained_slices"][filename] == dict(bytes=len(retained), sha256=digest(retained))
        retained_names.append(filename)
assert set(report["retained_slices"]) == set(retained_names)
assert digest((evidence / "full-preparation/check-full-public.py").read_bytes()) == "fd026aa62c8cf9f663f7a9066a66d1ea1021d0b88b980cebb7aa49dd0e94a3c7"
assert digest((evidence / "check-full-public.py").read_bytes()) == "fd026aa62c8cf9f663f7a9066a66d1ea1021d0b88b980cebb7aa49dd0e94a3c7"
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
required_true = json.loads('["ordinary_original_reconstruction_derived", "same_last_group_state_constructor_run", "raw_checked_makeNode_execute_two_derived", "fixed_model_stable_heap_transport_derived", "all_ambient_physical_parent_equivalence_derived"]')
required_false = json.loads('["future_success_premise", "fresh_key_width_safety_claimed", "generated_root_admission_claimed", "model_rebase_claimed", "mu_reconstruction_claimed", "public_pass_claimed", "haskell_refinement_claimed", "whole_goal_complete", "whole_body_manual_read_claimed"]')
assert all(review[key] is True for key in required_true) and all(review[key] is False for key in required_false)
audit = (evidence / (audit_stem + ".log")).read_text()
build = re.search(r"Build completed successfully \((\d+) jobs\)\.", audit)
dependencies = re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", audit)
assert build and dependencies and not re.search(r"\berror(?:\([^)]*\))?:", audit)
assert int(build.group(1)) == int("3640") and int(dependencies.group(1)) == int("75501")
print(json.dumps(dict(status="PASS", live=args.live, **metrics, new_lean_lake_jobs=0, selected_modules=1, original_archives=1,
    public_definitions=sum(kind == "def" for _, kind in specs), public_theorems=sum(kind == "theorem" for _, kind in specs), audit_build_jobs=int(build.group(1)), audit_dependencies=int(dependencies.group(1)), audit_log_sha256=digest(audit.encode())), indent=2))
