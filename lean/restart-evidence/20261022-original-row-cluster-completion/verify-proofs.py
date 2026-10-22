"""Check saved original-row cluster-completion evidence. This script does not run Lean."""
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
evidence = root / "lean/restart-evidence/20261022-original-row-cluster-completion"
def load(name):
    return json.loads((evidence / name).read_text())
def digest(data):
    return hashlib.sha256(data).hexdigest()
name, head = "SourceCurrentOriginalRowClusterCompletion", "MicroCFTA.SourceCurrentOriginalRowClusterCompletion.cluster_complete"
selected_sha = "c6e8e0f7f819d1c595ff6d56c160558bff837a86196ad2c951524d93a70c9a9b"
source_lines = int("345")
strict_stem, full_stem, audit_stem = "original-row-cluster-completion-strict-3", "original-row-cluster-completion-public-1", "original-row-cluster-completion-audit-1"
metrics = dict(actual_jobs=int("5"), source_jobs=int("4"), audit_jobs=int("1"),
    failed_jobs=int("2"), warned_source_exit_zero_jobs=int("0"),
    rejected_public_type_jobs=int("0"))
jobs = json.loads('{"original-row-cluster-completion-audit-1": [0, null, "aa655ae2759fb973a0e3846f04c00f96c8bf7d8b105817e29a6d899d1d558e74", 0, 0], "original-row-cluster-completion-public-1": [0, "7559984efcf32c0aa207c6ab2d3be0a478aed3d356e6d1ce69c5d5ddaba50039", "499c648f0ac8f0e69fa9bd78e16d7c95dd39d3c4442ee5a07188404260518ac5", 0, 0], "original-row-cluster-completion-strict-1": [1, "aa72ddb54eeb5a06123af80983c269e5c8aef1bded4f446e65de99fa80e69ec0", "6def86a8b3726593c81c9ed715d7853a288bb4bd8356e8af8059b70a01c4bc67", 13, 0], "original-row-cluster-completion-strict-2": [1, "467e909e1d5c76e2c9cd88c3fa71620635ad3585bb29dbe813825c74f6ecb9c5", "da6cbaa6336035634a7be027b8cfe628208e786ebb4cfb0cee16d62f8fe182a4", 2, 0], "original-row-cluster-completion-strict-3": [0, "c6e8e0f7f819d1c595ff6d56c160558bff837a86196ad2c951524d93a70c9a9b", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", 0, 0]}')
rejected = json.loads('[]')
assert jobs and all(stem.startswith("original-row-cluster-completion-") for stem in jobs)
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
        assert digest(source) == source_hash and Path(receipt["command"][-1]).name == receipt["source"]
        assert len(receipt["command"]) == 3 and Path(receipt["command"][0]).name == "lean" and receipt["command"][1] == "-Dlinter.all=true"
        assert len(re.findall(r"^.+?:\d+:\d+: error(?:\([^)]*\))?:", raw.decode(), re.M)) == errors
        assert len(re.findall(r"^.+?:\d+:\d+: warning(?:\([^)]*\))?:", raw.decode(), re.M)) == warnings
        if "public" not in stem:
            assert not re.search(r"^\s*set_option (?:maxHeartbeats|maxRecDepth|linter\.)", source.decode(), re.M)
    else:
        assert Path(receipt["command"][0]).name == "lake" and receipt["command"][-2:] == ["build", "MicroCFTA.Audit"]
strict_source = (evidence / (strict_stem + ".source.lean")).read_bytes()
assert len(strict_source.splitlines()) == source_lines <= 350
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
assert history == json.loads('{"artifacts": [{"bytes": 622, "path": "original-row-cluster-completion-audit-1.json", "sha256": "b9ec860c787644631c65f60a85b55bdfb6d28846f365c2dc648f675ea61ce71c"}, {"bytes": 90, "path": "original-row-cluster-completion-audit-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"bytes": 697, "path": "original-row-cluster-completion-audit-1.log", "sha256": "aa655ae2759fb973a0e3846f04c00f96c8bf7d8b105817e29a6d899d1d558e74"}, {"bytes": 114, "path": "original-row-cluster-completion-audit-1.usage.json", "sha256": "8f1602837b73306bd0f83bf8e61f89bc66c4d80b6bbe5c458292d9450fff03be"}, {"bytes": 862, "path": "original-row-cluster-completion-public-1.json", "sha256": "f080c9d70cb87dba06b0fb19756a5b0521d8e0d542882fe6743af57f952dd2c0"}, {"bytes": 90, "path": "original-row-cluster-completion-public-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"bytes": 4682784, "path": "original-row-cluster-completion-public-1.log", "sha256": "499c648f0ac8f0e69fa9bd78e16d7c95dd39d3c4442ee5a07188404260518ac5"}, {"bytes": 22312, "path": "original-row-cluster-completion-public-1.source.lean", "sha256": "7559984efcf32c0aa207c6ab2d3be0a478aed3d356e6d1ce69c5d5ddaba50039"}, {"bytes": 114, "path": "original-row-cluster-completion-public-1.usage.json", "sha256": "a04f18985791b906a08ea142e1d0d4a44a094194082ec954bca35f9f339dd488"}, {"bytes": 862, "path": "original-row-cluster-completion-strict-1.json", "sha256": "51ed9da69d3e9deeefc70163037d4df05af3605baedae22dae4f74167d846f3a"}, {"bytes": 90, "path": "original-row-cluster-completion-strict-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"bytes": 6884, "path": "original-row-cluster-completion-strict-1.log", "sha256": "6def86a8b3726593c81c9ed715d7853a288bb4bd8356e8af8059b70a01c4bc67"}, {"bytes": 114, "path": "original-row-cluster-completion-strict-1.usage.json", "sha256": "18b70ff58b5c3bde335ddafd073ceb3e8230c49e00ce8b59f28f621b9dccf5c7"}, {"bytes": 862, "path": "original-row-cluster-completion-strict-2.json", "sha256": "588412af4694c199a0e8f31108830ab52885aa54209fb110ce1207d2bc5290c9"}, {"bytes": 90, "path": "original-row-cluster-completion-strict-2.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"bytes": 8046, "path": "original-row-cluster-completion-strict-2.log", "sha256": "da6cbaa6336035634a7be027b8cfe628208e786ebb4cfb0cee16d62f8fe182a4"}, {"bytes": 114, "path": "original-row-cluster-completion-strict-2.usage.json", "sha256": "092f7fb503eb53abcbfc748a6a71be1f1c06dd2745535ba4d03dc5f087a59e8c"}, {"bytes": 862, "path": "original-row-cluster-completion-strict-3.json", "sha256": "fcf0aecf354cd0c51010ed0eb21b537fbed93503e59b4def98b23b5550225152"}, {"bytes": 90, "path": "original-row-cluster-completion-strict-3.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"bytes": 0, "path": "original-row-cluster-completion-strict-3.log", "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"}, {"bytes": 114, "path": "original-row-cluster-completion-strict-3.usage.json", "sha256": "f414ff6e01fe1de6aae7bfed54d4fbd2b2c2987cf709a4a93b6b715febb74cd9"}, {"bytes": 1081, "path": "signature-plan/context.lean.txt", "sha256": "030321d534ea36df66458e3cfba14e0cf183c9e6c85e2930252c93dabaf127b3"}, {"bytes": 3288, "path": "source-proposal/preflight.patch", "sha256": "12b3c507fde562f2e7d4420ba420ab8df0d4f09ef93475aed9f83db7c4adec9d"}, {"bytes": 22126, "path": "source-proposal/source-addition.patch", "sha256": "cdfc590d609ce1bf52f05d85f14dcdc803e54038d3f6f3a7de09cfc6ddd8698f"}, {"bytes": 1103, "path": "source-repair-v2/context.lean.txt", "sha256": "b33ff6c3d1d1a727389ef150fbde8516e9d622c43901e900a7a08d82658c9f3a"}, {"bytes": 4111, "path": "source-repair-v2/repair.patch", "sha256": "8b4d7a698f92992f5bf650b3006448f86bb8e4beb69f5c04958110009cdb20f3"}, {"bytes": 1231, "path": "source-repair-v3/repair.patch", "sha256": "efcc3b452d19566a4e014aae7ef16573073a980952bff36f9d5d2aef7e5e2b33"}], "patches": [{"after": "original-row-cluster-completion-strict-1.source.lean", "before": "source-proposal/draft-1/SourceCurrentOriginalRowClusterCompletion.lean", "fromfile": "draft-1/SourceCurrentOriginalRowClusterCompletion.lean", "path": "source-proposal/preflight.patch", "sha256": "12b3c507fde562f2e7d4420ba420ab8df0d4f09ef93475aed9f83db7c4adec9d", "tofile": "SourceCurrentOriginalRowClusterCompletion.lean"}, {"after": "original-row-cluster-completion-strict-2.source.lean", "before": "original-row-cluster-completion-strict-1.source.lean", "fromfile": "original/SourceCurrentOriginalRowClusterCompletion.lean", "path": "source-repair-v2/repair.patch", "sha256": "8b4d7a698f92992f5bf650b3006448f86bb8e4beb69f5c04958110009cdb20f3", "tofile": "SourceCurrentOriginalRowClusterCompletion.lean"}, {"after": "original-row-cluster-completion-strict-3.source.lean", "before": "original-row-cluster-completion-strict-2.source.lean", "fromfile": "original-v2/SourceCurrentOriginalRowClusterCompletion.lean", "path": "source-repair-v3/repair.patch", "sha256": "efcc3b452d19566a4e014aae7ef16573073a980952bff36f9d5d2aef7e5e2b33", "tofile": "SourceCurrentOriginalRowClusterCompletion.lean"}], "rejected_public_types": [], "selected_source_sha256": "c6e8e0f7f819d1c595ff6d56c160558bff837a86196ad2c951524d93a70c9a9b", "status": "ROOT_ACCEPTED", "variants": [{"lines": 340, "path": "source-proposal/draft-1/SourceCurrentOriginalRowClusterCompletion.lean", "sha256": "65198df3d26ee22a76874a0c97441a803bf1c2950f117ccd47eee8f1d5f3a29b"}, {"lines": 344, "path": "original-row-cluster-completion-strict-1.source.lean", "sha256": "aa72ddb54eeb5a06123af80983c269e5c8aef1bded4f446e65de99fa80e69ec0"}, {"lines": 344, "path": "original-row-cluster-completion-strict-2.source.lean", "sha256": "467e909e1d5c76e2c9cd88c3fa71620635ad3585bb29dbe813825c74f6ecb9c5"}, {"lines": 345, "path": "original-row-cluster-completion-strict-3.source.lean", "sha256": "c6e8e0f7f819d1c595ff6d56c160558bff837a86196ad2c951524d93a70c9a9b"}]}') and history["status"] == "ROOT_ACCEPTED"
assert history["selected_source_sha256"] == selected_sha
variants = {item["path"]: item for item in history["variants"]}
artifacts = {item["path"]: item for item in history["artifacts"]}
assert variants and len(variants) == len(history["variants"]) and len(artifacts) == len(history["artifacts"])
for path, item in {**artifacts, **variants}.items():
    relative = Path(path)
    assert not relative.is_absolute() and ".." not in relative.parts
    data = (evidence / relative).read_bytes()
    assert re.fullmatch(r"[0-9a-f]{64}", item["sha256"]) and digest(data) == item["sha256"]
    if path in variants:
        assert 0 < len(data.splitlines()) == item["lines"] <= 350
    else:
        assert len(data) == item["bytes"]
assert not set(variants) & set(artifacts)
assert any((evidence / path).read_bytes() == source for path in variants)
for stem, row in jobs.items():
    if row[1] and "public" not in stem:
        assert any(pin["sha256"] == row[1] and (evidence / path).read_bytes() == (evidence / (stem + ".source.lean")).read_bytes() for path, pin in variants.items()), stem
for patch in history["patches"]:
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
failed_stem = "original-row-cluster-completion-strict-1"
assert jobs[failed_stem] == [1, "aa72ddb54eeb5a06123af80983c269e5c8aef1bded4f446e65de99fa80e69ec0", "6def86a8b3726593c81c9ed715d7853a288bb4bd8356e8af8059b70a01c4bc67", 13, 0]
original_context = (evidence / "signature-plan/context.lean.txt").read_bytes()
assert digest(original_context) == "030321d534ea36df66458e3cfba14e0cf183c9e6c85e2930252c93dabaf127b3" and len(original_context.splitlines()) == 17
assert (evidence / (failed_stem + ".source.lean")).read_bytes().startswith(original_context)
contracts = {'context.lean.txt': (17, 'b33ff6c3d1d1a727389ef150fbde8516e9d622c43901e900a7a08d82658c9f3a'), 'private-prefix-signature.lean.txt': (7, '36f9082d97a6b46ec650e7f23ecc8746a5b0500125f01d2484e7aaea1a7af758'), 'private-scan-signature.lean.txt': (62, '3de19f0087e5ed03597db0bce974ee0eed0d09f388f8381df1d0eb2b230ebc87'), 'proposed-signature.lean.txt': (51, '8783abbab974ac01cedc351d3363e0540405fa2b40064e68baefe77d659deb47')}
positions = []
for filename, (lines, expected_hash) in contracts.items():
    path = "source-repair-v2/context.lean.txt" if filename == "context.lean.txt" else "signature-plan/" + filename
    declaration = (evidence / path).read_bytes()
    assert digest(declaration) == expected_hash and len(declaration.splitlines()) == lines
    if filename == "context.lean.txt":
        assert source.startswith(declaration)
    else:
        literal = declaration.rstrip(b"\n") + b" := by\n"
        assert source.count(literal) == 1
        positions.append(source.index(literal))
assert positions == sorted(positions) and len(set(positions)) == 3
assert re.findall(r"^(?:private )?(?:noncomputable )?(?:def|theorem|lemma|abbrev|opaque|structure|inductive|instance) (\w+)", source.decode(), re.M) == ["execute_yielded_add", "scan_boundary_complete", "cluster_complete"]
if args.live:
    assert (root / source_path).read_bytes() == source
original = (evidence / "original-sources/Audit.original.lean.txt").read_bytes()
assert digest(original) == "2fc4ad7d7e708d0601a46c6053f436be92e7fb03b7be78098ec66a2b9c86a698" and len(original.splitlines()) == 3122
assert load("original-source-index.json")["sources"] == [dict(path="lean/MicroCFTA/Audit.lean", snapshot="original-sources/Audit.original.lean.txt", lines=3122, sha256=digest(original))]
addition = b"import MicroCFTA.SourceCurrentOriginalRowClusterCompletion\n"
audit_source = (root / "lean/MicroCFTA/Audit.lean").read_bytes()
assert audit_source.count(addition) == 1 and audit_source.replace(addition, b"", 1) == original
assert audit_source.index(addition) < audit_source.index(b"/-!")
report = load("public-readback/original-row-cluster-completion-full-readback.json")
printer = (evidence / (full_stem + ".source.lean")).read_bytes()
raw = (evidence / (full_stem + ".log")).read_bytes()
options = ["maxRecDepth 30000", "maxHeartbeats 0", "linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true",
    "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]
tail = "\n" + "".join("set_option " + option + "\n" for option in options) + "".join(d + head + "\n" for d in ["#check @", "#print ", "#print axioms "])
assert printer == source + tail.encode() and len(printer.splitlines()) == source_lines + 14 and len(tail.splitlines()) == 14
assert all(printer.decode().splitlines().count("set_option " + option) == 1 for option in options)
assert all(printer.decode().splitlines().count(d + head) == 1 for d in ["#check @", "#print ", "#print axioms "])
assert source.rstrip().endswith(("end MicroCFTA." + name).encode())
assert (report["source_sha256"], report["source_lines"], report["printer_sha256"]) == (selected_sha, source_lines, digest(printer))
assert report["log_sha256"] == digest(raw) and report["log_bytes"] == len(raw) == int("4682784")
assert report["receipt_sha256"] == digest((evidence / (full_stem + ".json")).read_bytes()) and report["owned_public_job_exit"] == 0
assert all(report[key] for key in ["all_eight_printer_settings", "exact_module_and_diagnostic_tail", "diagnostic_limits_after_module_only", "no_omissions"])
assert len(report["heads"]) == 1 and report["heads"][0]["head"] == head and report["heads"][0]["kind"] == "theorem"
log = raw.decode()
assert not re.search(r"sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.", log)
markers = list(re.finditer(r"^(?:@)?" + re.escape(head) + r" :", log, re.M))
assert len(markers) == 1 and not log[:markers[0].start()].strip()
segment = log[markers[0].end():]
assert segment.count("\ntheorem " + head + " :") == 1
checked, printed = segment.split("\ntheorem " + head + " :", 1)
axioms = list(re.finditer(r"^'" + re.escape(head) + r"' (depends on axioms:|does not depend on any axioms)", printed, re.M))
assert len(axioms) == 1
axiom = axioms[0]
declaration, axiom_output = printed[:axiom.start()], printed[axiom.start():]
normalized, matches = "".join(checked.split()), []
for match in re.finditer(r" :=\n", declaration):
    prefix = "".join(declaration[:match.start()].split())
    if prefix == normalized:
        matches.append(match)
    elif len(prefix) > len(normalized):
        break
assert len(matches) == 1
declared, body = declaration[:matches[0].start()], declaration[matches[0].end():]
assert checked.encode() == declared.encode() and len(checked) == int("57627") and len(checked.encode()) == int("57667")
assert len(checked.splitlines()) == int("618") and checked.count("\n") == int("617") and checked.endswith("\n") == json.loads('false')
assert digest(checked.encode()) == "89d3dbda3fc24202f94a9126aa10d9022226455cb91817365798aa1875d128fa"
assert not any(token in checked for token in ["_private", "✝", "†", "‡"])
helpers = re.findall(r"^private (?:noncomputable )?(?:def|theorem|abbrev) (\w+)", source.decode(), re.M)
assert helpers == ["execute_yielded_add", "scan_boundary_complete"]
assert not any(re.search(re.escape("MicroCFTA." + name + "." + helper) + r"(?![\w'])", checked) for helper in helpers)
head_report = report["heads"][0]
assert all(head_report[key] for key in ["check_print_type_identity", "check_print_type_byte_identity", "unique_complete_type_body_delimiter", "actual_axioms_within_standard_allowed"])
assert head_report["private_namespace_helpers_checked"] == helpers and head_report["private_type_spellings_checked"] == ["_private", "✝", "†", "‡"] and head_report["private_public_type_names"] is False
assert head_report["checked_type_characters"] == len(checked) and head_report["body_characters"] == len(body) == int("4566704")
assert body.startswith("fun ") and len(body.encode()) == int("4567156")
values = re.fullmatch(r"\s*\[([^\]]*)\]\s*", printed[axiom.end():]) if axiom.group(1) == "depends on axioms:" else None
assert values or (axiom.group(1) == "does not depend on any axioms" and not printed[axiom.end():].strip())
actual_axioms = {re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in values.group(1).split(",") if item.strip()} if values else set()
assert actual_axioms == set(head_report["actual_axioms"]) == set(json.loads('["Classical.choice", "Quot.sound", "propext"]')) and actual_axioms <= {"Classical.choice", "Quot.sound", "propext"}
for suffix, text in [("public-type", checked), ("printed-public-type", declared), ("body", body), ("axioms", axiom_output)]:
    filename = "original-row-cluster-completion-cluster_complete-" + suffix + ".txt"
    retained = (evidence / "public-readback" / filename).read_bytes()
    assert retained == text.encode() and report["retained_slices"][filename] == dict(bytes=len(retained), sha256=digest(retained))
assert digest((evidence / "full-preparation/check-full-public.py").read_bytes()) == "e4dc3549010f5bfba7301c4aea86baf757d678199103d36ab5272a020256c7a3"
review = load("root-full-review.json")
assert review["status"] == "ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT" and review["source_sha256"] == selected_sha and review["source_lines"] == source_lines
assert review["public_theorem"] == head and review["complete_public_type_root_review"] == review["independent_complete_public_type_review"] == "CLEAR"
assert review["root_read_complete_public_type"] and review["root_printed_type_byte_identity_verified"] and review["check_print_type_byte_identity"] and review["four_private_markers_and_all_helpers_absent_from_type"]
assert review["type_sha256"] == digest(checked.encode()) and review["full_raw_sha256"] == digest(raw) and review["actual_axioms"] == sorted(actual_axioms)
assert review["body_retained_and_programmatically_checked"] and review["whole_body_manual_read_claimed"] is False
required_true = ['actual_cluster_completion_derived', 'exact_original_parent_filtered_group', 'original_membership_length', 'same_returned_full_state', 'fixed_source_view_model_ranks_width', 'same_initial_domain_cache_and_global_trace', 'same_initial_reservation_retained', 'good_contextual_semantic_stable_idle_retained', 'native_extension_pair_extends_returned_retained', 'effects_composed_at_consecutive_states', 'candidate_identity_before_pivot_identity', 'promotion_reconstruction_order_preserved', 'generated_common_not_later_operand', 'noncomputable_operational_model']
required_false = ['future_success_premise', 'comparison_callback_premise', 'semantic_completion_premise', 'word_ranges_premise', 'post_room_premise', 'desired_semantic_law_premise', 'generated_parent_oracle', 'ordered_sublist_claimed', 'pairwise_maximality_claimed', 'physical_language_iff_claimed', 'haskell_refinement_claimed', 'generated_parent_completion_claimed', 'mu_full_pass_claimed', 'whole_goal_complete']
assert all(review[key] is True for key in required_true) and all(review[key] is False for key in required_false)
audit = (evidence / (audit_stem + ".log")).read_text()
build = re.search(r"Build completed successfully \((\d+) jobs\)\.", audit)
dependencies = re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", audit)
assert build and dependencies and not re.search(r"\berror(?:\([^)]*\))?:", audit)
assert int(build.group(1)) == int("3634") and int(dependencies.group(1)) == int("75451")
print(json.dumps(dict(status="PASS", live=args.live, **metrics, new_lean_lake_jobs=0, selected_modules=1, original_archives=1,
    audit_build_jobs=int(build.group(1)), audit_dependencies=int(dependencies.group(1)), audit_log_sha256=digest(audit.encode())), indent=2))
