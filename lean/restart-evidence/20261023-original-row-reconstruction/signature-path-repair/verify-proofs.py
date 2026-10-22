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
name = "__H23_MODULE_NAME__"
namespace = "MicroCFTA." + name + "."
specs = json.loads("__H23_PUBLIC_SPECS_JSON__")
short_names = [short for short, kind in specs]
selected_sha = "__H23_SELECTED_SOURCE_SHA__"
source_lines = int("__H23_SOURCE_LINES__")
strict_stem, full_stem, audit_stem = "__H23_SELECTED_STRICT_STEM__", "__H23_SELECTED_FULL_STEM__", "__H23_AUDIT_STEM__"
metrics = dict(actual_jobs=int("__H23_ACTUAL_JOBS__"), source_jobs=int("__H23_SOURCE_JOBS__"), audit_jobs=int("__H23_AUDIT_JOBS__"),
    failed_jobs=int("__H23_FAILED_JOBS__"), warned_source_exit_zero_jobs=int("__H23_WARNED_SOURCE_EXIT_ZERO_JOBS__"),
    rejected_public_type_jobs=int("__H23_REJECTED_PUBLIC_TYPE_JOBS__"))
jobs = json.loads("__H23_JOBS_JSON__")
rejected = json.loads("__H23_REJECTED_PUBLIC_STEMS_JSON__")
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
assert len(strict_source.splitlines()) == source_lines <= int("__H23_SOURCE_HARD_STOP__")
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
assert history == json.loads("__H23_SOURCE_HISTORY_JSON__") and history["status"] == "ROOT_ACCEPTED"
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
        assert 0 < len(data.splitlines()) == item["lines"] <= int("__H23_SOURCE_HARD_STOP__") and isinstance(item["reason"], str) and item["reason"].strip()
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
contracts = json.loads("__H23_CONTRACTS_JSON__")
expected_contracts = json.loads("__H23_CONTRACTS_JSON__")
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
assert helpers == json.loads("__H23_PRIVATE_NAMES_JSON__"), "Only the approved H23 private helpers are permitted"
declaration_review = load("root-declaration-review.json")
assert declaration_review["status"] == "ROOT_DECLARATION_REVIEW_CLEAR"
assert declaration_review["module"] == "MicroCFTA." + name
assert declaration_review["public_names"] == short_names and declaration_review["private_names"] == helpers
assert declaration_review.get("local_induction") == json.loads("__H23_LOCAL_INDUCTION_JSON__")
assert declaration_review["source_hard_stop"] == int("__H23_SOURCE_HARD_STOP__")
assert declaration_review["contract_sha256"] == "__H23_CONTRACT_SHA256__"
assert digest((evidence / "signature-repair/contracts.json").read_bytes()) == declaration_review["contract_sha256"]
assert [{key: item[key] for key in ["path", "lines", "sha256"]} for item in declaration_review["contracts"]] == [dict(path=filename, lines=item["lines"], sha256=item["sha256"]) for filename, item in expected_contracts.items()]
if args.live:
    assert (root / source_path).read_bytes() == source
original = (evidence / "original-sources/Audit.original.lean.txt").read_bytes()
assert digest(original) == "ebcc4770268c142e8fb5370dadcbf9be224276f4c7b0240c9876df55444715de" and len(original.splitlines()) == 3128
assert load("original-source-index.json")["sources"] == [dict(path="lean/MicroCFTA/Audit.lean", snapshot="original-sources/Audit.original.lean.txt", lines=3128, sha256=digest(original))]
addition = b"import MicroCFTA.__H23_MODULE_NAME__\n"
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
assert report["log_sha256"] == digest(raw) and report["log_bytes"] == len(raw) == int("__H23_FULL_RAW_BYTES__")
assert report["receipt_sha256"] == digest((evidence / (full_stem + ".json")).read_bytes()) and report["owned_public_job_exit"] == 0
assert all(report[key] for key in ["all_eight_printer_settings", "exact_module_and_diagnostic_tail", "diagnostic_limits_after_module_only", "no_omissions"])
assert (report["pp_option_count"], report["linter_option_count"], report["diagnostic_limit_count"]) == (7, 1, 2)
assert report["configured_paths"] == {key: str(path.resolve()) for key, path in dict(source=evidence / (name + ".lean"), printer=evidence / (full_stem + ".source.lean"), raw=evidence / (full_stem + ".log"), receipt=evidence / (full_stem + ".json")).items()}
assert [(item["head"], item["kind"]) for item in report["heads"]] == [(namespace + short, kind) for short, kind in specs]
head_metrics = json.loads("__H23_HEAD_METRICS_JSON__")
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
assert digest((evidence / "full-preparation/check-full-public.py").read_bytes()) == "__H23_FULL_READER_SHA__"
assert digest((evidence / "check-full-public.py").read_bytes()) == "__H23_FULL_READER_SHA__"
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
required_true = json.loads("__H23_SCOPE_TRUE_KEYS_JSON__")
required_false = json.loads("__H23_SCOPE_FALSE_KEYS_JSON__")
assert all(review[key] is True for key in required_true) and all(review[key] is False for key in required_false)
audit = (evidence / (audit_stem + ".log")).read_text()
build = re.search(r"Build completed successfully \((\d+) jobs\)\.", audit)
dependencies = re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", audit)
assert build and dependencies and not re.search(r"\berror(?:\([^)]*\))?:", audit)
assert int(build.group(1)) == int("__H23_AUDIT_BUILD_JOBS__") and int(dependencies.group(1)) == int("__H23_AUDIT_DEPENDENCIES__")
print(json.dumps(dict(status="PASS", live=args.live, **metrics, new_lean_lake_jobs=0, selected_modules=1, original_archives=1,
    public_definitions=sum(kind == "def" for _, kind in specs), public_theorems=sum(kind == "theorem" for _, kind in specs), audit_build_jobs=int(build.group(1)), audit_dependencies=int(dependencies.group(1)), audit_log_sha256=digest(audit.encode())), indent=2))
