"""Check saved direct edge-body word-range evidence. This script does not run Lean."""
import argparse
import hashlib
import json
import re
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--root", required=True, type=Path)
parser.add_argument("--live", action="store_true")
args = parser.parse_args()
root = args.root.resolve()
evidence = root / "lean/restart-evidence/20261022-direct-edge-word-ranges"
def load(name):
    return json.loads((evidence / name).read_text())
def digest(data):
    return hashlib.sha256(data).hexdigest()
name, head = "SourceCurrentAllocatedDirectEdgeWordRanges", "MicroCFTA.SourceCurrentAllocatedDirectEdgeWordRanges.edge_body"
selected_sha = "de874220ae0aab490300f809c9fa4d2a931030fd69b95efb70deaa9a92a4b440"
source_lines = int("44")
metrics = dict(actual_jobs=int("3"), source_jobs=int("2"), audit_jobs=int("1"),
    failed_jobs=int("0"), warned_source_exit_zero_jobs=int("0"),
    rejected_public_type_jobs=int("0"))
jobs = {
    "direct-edge-word-ranges-strict-1": (0, selected_sha, digest(b""), 0, 0),
    "direct-edge-word-ranges-public-1": (0, "63555e5ba4a4057f73c1bbd4290e700fb7d87221f83336ef1ca58dbf8d43eb0d", "601da48ea93ac39607b0dfcba89840530cacb5ac1d5127e67a0dbf01b1b7fb58", 0, 0),
    "direct-edge-word-ranges-audit-1": (0, None, "3fa06af51ce38d71a9b3774fc3c29e0e422ca4a8b27b8de4512de536e2994202", None, None),
}
assert (evidence / "direct-edge-word-ranges-audit-1.json").is_file(), "Audit is pending; no complete proof report is available"
actual = set()
for path in evidence.glob("*.json"):
    item = json.loads(path.read_text())
    if isinstance(item, dict) and "wrapper" in item and "exit_code" in item:
        if Path(item.get("command", [""])[0]).name in {"lean", "lake"}:
            actual.add(path.stem)
assert actual == set(jobs), actual
assert metrics["actual_jobs"] == len(actual) and metrics["source_jobs"] == 2 and metrics["audit_jobs"] == 1
assert metrics["failed_jobs"] == metrics["warned_source_exit_zero_jobs"] == metrics["rejected_public_type_jobs"] == 0
for stem, (exit_code, source_hash, log_hash, errors, warnings) in jobs.items():
    receipt = load(stem + ".json")
    assert receipt["exit_code"] == exit_code and receipt["log"] == stem + ".log" and receipt["observed_at"]
    raw = (evidence / receipt["log"]).read_bytes()
    if log_hash:
        assert digest(raw) == log_hash, stem
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
        assert len(re.findall(r"^.+?:\d+:\d+: error:", raw.decode(), re.M)) == errors
        assert len(re.findall(r"^.+?:\d+:\d+: warning:", raw.decode(), re.M)) == warnings
        if "strict" in stem:
            assert not re.search(r"^set_option (?:maxHeartbeats|maxRecDepth|linter\.)", source.decode(), re.M)
    else:
        assert Path(receipt["command"][0]).name == "lake" and receipt["command"][-2:] == ["build", "MicroCFTA.Audit"]
stricts = [(evidence / ("direct-edge-word-ranges-strict-" + str(i) + ".source.lean")).read_text() for i in [1]]
assert [len(source.splitlines()) for source in stricts] == [source_lines]
assert (evidence / "direct-edge-word-ranges-strict-1.log").read_bytes() == b""
selection = load("selected-sources.json")
source_path = "lean/MicroCFTA/" + name + ".lean"
assert selection == {source_path: dict(sha256=selected_sha, lines=source_lines, strict="direct-edge-word-ranges-strict-1", full="direct-edge-word-ranges-public-1")}
source = (evidence / (name + ".lean")).read_bytes()
drafts = evidence / "drafts"
original_draft = (drafts / "SourceCurrentAllocatedDirectEdgeWordRanges.source.lean.txt").read_bytes()
qualified_draft = (drafts / "SourceCurrentAllocatedDirectEdgeWordRanges.source-v2.lean.txt").read_bytes()
assert digest(original_draft) == "af3a4b1e1a4b27e5e0ab0d84026908dc2ad4f08720caf1240f5e3e7254d11304"
assert digest(qualified_draft) == "de874220ae0aab490300f809c9fa4d2a931030fd69b95efb70deaa9a92a4b440"
assert len(original_draft.splitlines()) == len(qualified_draft.splitlines()) == 44
assert original_draft.count(b"=> EdgeResident after.heap value") == 1
assert original_draft.replace(b"=> EdgeResident after.heap value", b"=> InternedEdgeResidency.EdgeResident after.heap value", 1) == qualified_draft == source
precheck = load("drafts/source-qualification.json")
assert precheck["status"] == "PRECHECK_SOURCE_REPAIR" and precheck["proof_commands_executed"] == 0 and precheck["context_and_header_unchanged"]
assert digest((drafts / "source-qualification.patch").read_bytes()) == "9d00234f564dae12fc50f99e0bf66971806ff277aefbfcc48873f543b8edfa10"
assert digest(source) == selected_sha and source.decode() == stricts[0]
gate = load("selected-source-gate.json")
assert gate == dict(status="ROOT_ACCEPTED", path=source_path, sha256=selected_sha, lines=source_lines, snapshot="selected-sources/" + name + ".lean")
assert (evidence / gate["snapshot"]).read_bytes() == source
assert digest((evidence / "direct-edge-word-ranges-plan/context.lean.txt").read_bytes()) == "f28f0de521aa463a94afc400e61c355dad40b6666840cae7c857440679d92382"
assert source.startswith((evidence / "direct-edge-word-ranges-plan/context.lean.txt").read_bytes())
header = (evidence / "direct-edge-word-ranges-plan/proposed-signature.lean.txt").read_bytes()
assert len(header.splitlines()) == 15 and digest(header) == "1bfb6d4fc292eed41352a62809e29f03921c11e6787530c7d1ed036e1f538b93" and source.count(header.rstrip(b"\n") + b" := by\n") == 1
if args.live:
    assert (root / source_path).read_bytes() == source
original = (evidence / "original-sources/Audit.original.lean.txt").read_bytes()
assert digest(original) == "eb67f7c671837d434cc443c9bbe48e2a11bd54c66a3ffbd3bb2506884face11e" and len(original.splitlines()) == 3117
assert load("original-source-index.json")["sources"] == [dict(path="lean/MicroCFTA/Audit.lean", snapshot="original-sources/Audit.original.lean.txt", lines=3117, sha256=digest(original))]
addition = b"import MicroCFTA.SourceCurrentAllocatedDirectEdgeWordRanges\n"
audit_source = (root / "lean/MicroCFTA/Audit.lean").read_bytes()
assert audit_source.count(addition) == 1 and audit_source.replace(addition, b"", 1) == original
assert audit_source.index(addition) < audit_source.index(b"/-!")
report = load("public-readback/direct-edge-word-ranges-full-readback.json")
printer = (evidence / "direct-edge-word-ranges-public-1.source.lean").read_bytes()
raw = (evidence / "direct-edge-word-ranges-public-1.log").read_bytes()
options = ["maxRecDepth 30000", "maxHeartbeats 0", "linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true",
    "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]
tail = "\n" + "".join("set_option " + option + "\n" for option in options) + "".join(d + head + "\n" for d in ["#check @", "#print ", "#print axioms "])
assert printer == source + tail.encode() and len(printer.splitlines()) == source_lines + 14 and len(tail.splitlines()) == 14
assert all(printer.decode().splitlines().count("set_option " + option) == 1 for option in options)
assert all(printer.decode().splitlines().count(d + head) == 1 for d in ["#check @", "#print ", "#print axioms "])
assert source.rstrip().endswith(("end MicroCFTA." + name).encode())
assert (report["source_sha256"], report["source_lines"], report["printer_sha256"]) == (selected_sha, source_lines, digest(printer))
assert report["log_sha256"] == digest(raw) and report["log_bytes"] == len(raw) == int("129676")
assert report["receipt_sha256"] == digest((evidence / "direct-edge-word-ranges-public-1.json").read_bytes()) and report["owned_public_job_exit"] == 0
assert all(report[key] for key in ["all_eight_printer_settings", "exact_module_and_diagnostic_tail", "diagnostic_limits_after_module_only", "no_omissions"])
assert len(report["heads"]) == 1 and report["heads"][0]["head"] == head and report["heads"][0]["kind"] == "theorem"
log = raw.decode()
assert not re.search(r"sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.", log)
markers = list(re.finditer(r"^(?:@)?" + re.escape(head) + r" :", log, re.M))
assert len(markers) == 1 and not log[:markers[0].start()].strip()
checked, printed = log[markers[0].end():].split("\ntheorem " + head + " :", 1)
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
assert checked.encode() == declared.encode() and len(checked) == int("11701") and len(checked.encode()) == int("11721")
assert len(checked.splitlines()) == int("150") and checked.count("\n") == int("149") and not checked.endswith("\n")
assert digest(checked.encode()) == "dea801f02c35eb6ba68479e8fb93702264bf3b802aca8e06694683f988e9becf"
assert not any(token in checked for token in ["_private", "✝", "†", "‡"])
helpers = re.findall(r"^private (?:noncomputable )?(?:def|theorem|abbrev) (\w+)", source.decode(), re.M)
assert helpers == []
assert not any(re.search(re.escape("MicroCFTA." + name + "." + helper) + r"(?![\w'])", checked) for helper in helpers)
head_report = report["heads"][0]
assert all(head_report[key] for key in ["check_print_type_identity", "check_print_type_byte_identity", "unique_complete_type_body_delimiter", "actual_axioms_within_standard_allowed"])
assert head_report["private_namespace_helpers_checked"] == helpers and head_report["private_type_spellings_checked"] == ["_private", "✝", "†", "‡"] and head_report["private_public_type_names"] is False
assert head_report["checked_type_characters"] == len(checked) and head_report["body_characters"] == len(body) == int("105954")
assert body.startswith("fun ") and len(body.encode()) == int("105958")
values = re.fullmatch(r"\s*\[([^\]]*)\]\s*", printed[axiom.end():]) if axiom.group(1) == "depends on axioms:" else None
assert values or (axiom.group(1) == "does not depend on any axioms" and not printed[axiom.end():].strip())
actual_axioms = {re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in values.group(1).split(",") if item.strip()} if values else set()
assert actual_axioms == set(head_report["actual_axioms"]) == set(json.loads('["Classical.choice", "Quot.sound", "propext"]')) and actual_axioms <= {"Classical.choice", "Quot.sound", "propext"}
for suffix, text in [("public-type", checked), ("printed-public-type", declared), ("body", body), ("axioms", axiom_output)]:
    filename = "direct-edge-word-ranges-edge_body-" + suffix + ".txt"
    retained = (evidence / "public-readback" / filename).read_bytes()
    assert retained == text.encode() and report["retained_slices"][filename] == dict(bytes=len(retained), sha256=digest(retained))
assert digest((evidence / "full-preparation/check-full-public.py").read_bytes()) == "ee1487a1a62cec9137b7b62f3509dc30c370eede6c53428343650c487764017b"
review = load("root-full-review.json")
assert review["status"] == "ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT" and review["source_sha256"] == selected_sha and review["source_lines"] == source_lines
assert review["public_theorem"] == head and review["complete_public_type_root_review"] == review["independent_complete_public_type_review"] == "CLEAR"
assert review["root_read_both_complete_type_files"] and review["check_print_type_byte_identity"] and review["four_private_markers_and_all_helpers_absent_from_type"]
assert review["type_sha256"] == digest(checked.encode()) and review["full_raw_sha256"] == digest(raw) and review["actual_axioms"] == sorted(actual_axioms)
assert review["body_retained_and_programmatically_checked"] and review["whole_body_manual_read_claimed"] is False
assert review["word_ranges_derived"] and review["every_raw_steps_prefix"] and review["actual_source_current_readiness_and_room_premises"]
assert review["future_success_premise"] is False and review["native_completion_claimed"] is False
audit = (evidence / "direct-edge-word-ranges-audit-1.log").read_text()
build = re.search(r"Build completed successfully \((\d+) jobs\)\.", audit)
dependencies = re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", audit)
assert build and dependencies and not re.search(r"\berror(?:\([^)]*\))?:", audit)
assert int(build.group(1)) == int("3629") and int(dependencies.group(1)) == int("75380")
print(json.dumps(dict(status="PASS", live=args.live, **metrics, new_lean_lake_jobs=0, selected_modules=1, original_archives=1,
    audit_build_jobs=int(build.group(1)), audit_dependencies=int(dependencies.group(1)), audit_log_sha256=digest(audit.encode())), indent=2))
