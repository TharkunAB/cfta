"""Check saved fixed-source comparison domain-history evidence. This script does not run Lean."""
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
evidence = root / "lean/restart-evidence/20261022-same-symbol-edge-comparison-domains"
def load(name):
    return json.loads((evidence / name).read_text())
def digest(data):
    return hashlib.sha256(data).hexdigest()
name, head = "SourceCurrentSameSymbolEdgeComparisonDomains", "MicroCFTA.SourceCurrentSameSymbolEdgeComparisonDomains.original_rows_complete"
selected_sha = "__H15_SELECTED_SOURCE_SHA__"
source_lines = int("__H15_SOURCE_LINES__")
strict_stem, full_stem, audit_stem = "__H15_SELECTED_STRICT_STEM__", "__H15_SELECTED_FULL_STEM__", "__H15_AUDIT_STEM__"
metrics = dict(actual_jobs=int("__H15_ACTUAL_JOBS__"), source_jobs=int("__H15_SOURCE_JOBS__"), audit_jobs=int("__H15_AUDIT_JOBS__"),
    failed_jobs=int("__H15_FAILED_JOBS__"), warned_source_exit_zero_jobs=int("__H15_WARNED_SOURCE_EXIT_ZERO_JOBS__"),
    rejected_public_type_jobs=int("__H15_REJECTED_PUBLIC_TYPE_JOBS__"))
jobs = json.loads('__H15_JOBS_JSON__')
rejected = json.loads('__H15_REJECTED_PUBLIC_STEMS_JSON__')
assert jobs and all(stem.startswith("same-symbol-edge-comparison-domains-") for stem in jobs)
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
        if "strict" in stem:
            assert not re.search(r"^set_option (?:maxHeartbeats|maxRecDepth|linter\.)", source.decode(), re.M)
    else:
        assert Path(receipt["command"][0]).name == "lake" and receipt["command"][-2:] == ["build", "MicroCFTA.Audit"]
strict_source = (evidence / (strict_stem + ".source.lean")).read_bytes()
assert len(strict_source.splitlines()) == source_lines <= 250
assert (evidence / (strict_stem + ".log")).read_bytes() == b""
selection = load("selected-sources.json")
source_path = "lean/MicroCFTA/" + name + ".lean"
assert selection == {source_path: dict(sha256=selected_sha, lines=source_lines, strict=strict_stem, full=full_stem)}
source = (evidence / (name + ".lean")).read_bytes()
original_draft = (evidence / ("source-proposal/" + name + ".lean")).read_bytes()
assert digest(original_draft) == "8ae94566570cf99ec3eb61ec991d36a1df196c5b9c2bc2fca4aeb88fd6305e15" and len(original_draft.splitlines()) == 189
first_draft = (evidence / ("source-proposal/drafts/" + name + ".initial.lean.txt")).read_bytes()
assert digest(first_draft) == "bc86bb718462a95ad761e86041dd6bd56e05e9dfca499e91f7c00541b646682a" and len(first_draft.splitlines()) == 189
assert first_draft.replace(b"have prefix :=", b"have admitted :=", 1).replace(b"prefix.current.domains", b"admitted.current.domains", 1) == original_draft
assert digest((evidence / "source-proposal/preflight-name-fix.patch").read_bytes()) == "508618b907f2b9362ffff4cf420aeba8be0dff25c44afb2511c3e91975877472"
assert digest(source) == selected_sha and source == strict_source
gate = load("selected-source-gate.json")
assert gate == dict(status="ROOT_ACCEPTED", path=source_path, sha256=selected_sha, lines=source_lines, snapshot="selected-sources/" + name + ".lean")
assert (evidence / gate["snapshot"]).read_bytes() == source
assert digest((evidence / "source-proposal/context.lean.txt").read_bytes()) == "5528e9718f319b928ebaa78abe56dd1d128b11b421e0f13f6940e8f838827aad"
context = (evidence / "source-proposal/context.lean.txt").read_bytes()
assert len(context.splitlines()) == 16 and source.startswith(context) and original_draft.startswith(context)
header = (evidence / "source-proposal/proposed-signature.lean.txt").read_bytes()
assert len(header.splitlines()) == 56 and digest(header) == "4a094f0a81a7f98d72afc1bd1d7ed0b4b87c0b2a3352f9d6decd35586a855f23"
assert source.count(header.rstrip(b"\n") + b" := by\n") == original_draft.count(header.rstrip(b"\n") + b" := by\n") == 1
if args.live:
    assert (root / source_path).read_bytes() == source
original = (evidence / "original-sources/Audit.original.lean.txt").read_bytes()
assert digest(original) == "fa6c433f47dca1a9b5433edd416e98f742592352920ecd5969494e0b977d4d37" and len(original.splitlines()) == 3120
assert load("original-source-index.json")["sources"] == [dict(path="lean/MicroCFTA/Audit.lean", snapshot="original-sources/Audit.original.lean.txt", lines=3120, sha256=digest(original))]
addition = b"import MicroCFTA.SourceCurrentSameSymbolEdgeComparisonDomains\n"
audit_source = (root / "lean/MicroCFTA/Audit.lean").read_bytes()
assert audit_source.count(addition) == 1 and audit_source.replace(addition, b"", 1) == original
assert audit_source.index(addition) < audit_source.index(b"/-!")
report = load("public-readback/same-symbol-edge-comparison-domains-full-readback.json")
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
assert report["log_sha256"] == digest(raw) and report["log_bytes"] == len(raw) == int("__H15_FULL_RAW_BYTES__")
assert report["receipt_sha256"] == digest((evidence / (full_stem + ".json")).read_bytes()) and report["owned_public_job_exit"] == 0
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
assert checked.encode() == declared.encode() and len(checked) == int("__H15_TYPE_CHARACTERS__") and len(checked.encode()) == int("__H15_TYPE_BYTES__")
assert len(checked.splitlines()) == int("__H15_TYPE_LOGICAL_LINES__") and checked.count("\n") == int("__H15_TYPE_LINE_FEEDS__") and not checked.endswith("\n")
assert digest(checked.encode()) == "__H15_TYPE_SHA__"
assert not any(token in checked for token in ["_private", "✝", "†", "‡"])
helpers = re.findall(r"^private (?:noncomputable )?(?:def|theorem|abbrev) (\w+)", source.decode(), re.M)
assert helpers == ["original_of_readback", "rows_scope"]
assert not any(re.search(re.escape("MicroCFTA." + name + "." + helper) + r"(?![\w'])", checked) for helper in helpers)
head_report = report["heads"][0]
assert all(head_report[key] for key in ["check_print_type_identity", "check_print_type_byte_identity", "unique_complete_type_body_delimiter", "actual_axioms_within_standard_allowed"])
assert head_report["private_namespace_helpers_checked"] == helpers and head_report["private_type_spellings_checked"] == ["_private", "✝", "†", "‡"] and head_report["private_public_type_names"] is False
assert head_report["checked_type_characters"] == len(checked) and head_report["body_characters"] == len(body) == int("__H15_BODY_CHARACTERS__")
assert body.startswith("fun ") and len(body.encode()) == int("__H15_BODY_BYTES__")
values = re.fullmatch(r"\s*\[([^\]]*)\]\s*", printed[axiom.end():]) if axiom.group(1) == "depends on axioms:" else None
assert values or (axiom.group(1) == "does not depend on any axioms" and not printed[axiom.end():].strip())
actual_axioms = {re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in values.group(1).split(",") if item.strip()} if values else set()
assert actual_axioms == set(head_report["actual_axioms"]) == set(json.loads('__H15_ACTUAL_AXIOMS_JSON__')) and actual_axioms <= {"Classical.choice", "Quot.sound", "propext"}
for suffix, text in [("public-type", checked), ("printed-public-type", declared), ("body", body), ("axioms", axiom_output)]:
    filename = "same-symbol-edge-comparison-domains-original_rows_complete-" + suffix + ".txt"
    retained = (evidence / "public-readback" / filename).read_bytes()
    assert retained == text.encode() and report["retained_slices"][filename] == dict(bytes=len(retained), sha256=digest(retained))
assert digest((evidence / "full-preparation/check-full-public.py").read_bytes()) == "__H15_FULL_READER_SHA__"
review = load("root-full-review.json")
assert review["status"] == "ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT" and review["source_sha256"] == selected_sha and review["source_lines"] == source_lines
assert review["public_theorem"] == head and review["complete_public_type_root_review"] == review["independent_complete_public_type_review"] == "CLEAR"
assert review["root_read_complete_public_type"] and review["root_printed_type_byte_identity_verified"] and review["check_print_type_byte_identity"] and review["four_private_markers_and_all_helpers_absent_from_type"]
assert review["type_sha256"] == digest(checked.encode()) and review["full_raw_sha256"] == digest(raw) and review["actual_axioms"] == sorted(actual_axioms)
assert review["body_retained_and_programmatically_checked"] and review["whole_body_manual_read_claimed"] is False
assert review["original_closed_parent_rows"] and review["all_pair_lookup_cases_covered"] and review["same_current_operand_residency_derived"]
assert review["wrapper_completion_derived"] and review["final_stable_and_native_idle_derived"] and review["hit_checked_state_unchanged"]
assert review["native_receipt_on_hits_claimed"] is False
assert review["same_initial_domain_history_and_reservation_premises"] and review["current_room_derived"] and review["final_global_domain_history_derived"]
assert review["physical_language_iff_claimed"] is False and review["scan_completion_claimed"] is False
assert all(review[key] is False for key in ["future_success_premise", "semantic_completion_premise", "word_ranges_premise", "post_room_premise", "generated_parent_oracle"])
audit = (evidence / (audit_stem + ".log")).read_text()
build = re.search(r"Build completed successfully \((\d+) jobs\)\.", audit)
dependencies = re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", audit)
assert build and dependencies and not re.search(r"\berror(?:\([^)]*\))?:", audit)
assert int(build.group(1)) == int("__H15_AUDIT_BUILD_JOBS__") and int(dependencies.group(1)) == int("__H15_AUDIT_DEPENDENCIES__")
print(json.dumps(dict(status="PASS", live=args.live, **metrics, new_lean_lake_jobs=0, selected_modules=1, original_archives=1,
    audit_build_jobs=int(build.group(1)), audit_dependencies=int(dependencies.group(1)), audit_log_sha256=digest(audit.encode())), indent=2))
