"""Check saved original-row physical-meaning evidence. This script does not run Lean."""
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
evidence = root / "lean/restart-evidence/20261022-original-row-physical-meaning"
def load(name):
    return json.loads((evidence / name).read_text())
def digest(data):
    return hashlib.sha256(data).hexdigest()
name, head = "SourceCurrentOriginalRowPhysicalMeaning", "MicroCFTA.SourceCurrentOriginalRowPhysicalMeaning.row_inputs_meaning"
selected_sha = "b3c2aba3c1faf072e318feb7adb07f2b1d60970e4584354ef6584566e053d58e"
source_lines = int("108")
strict_stem, full_stem, audit_stem = "original-row-physical-meaning-strict-1", "original-row-physical-meaning-public-1", "original-row-physical-meaning-audit-1"
metrics = dict(actual_jobs=int("3"), source_jobs=int("2"), audit_jobs=int("1"),
    failed_jobs=int("0"), warned_source_exit_zero_jobs=int("0"),
    rejected_public_type_jobs=int("0"))
jobs = json.loads('{"original-row-physical-meaning-audit-1": [0, null, "466693d2927694094f94b53a0c86ac875b0800da9109b6793c621acdc6d3a0f9", 0, 0], "original-row-physical-meaning-public-1": [0, "cfe7e86855615e4366e66954939927197483e04ce96a461ec89bd4abb434f328", "4ec965e2d50131b88922ad5a3ca21d9a56212860c26474122f885e05b58ada4c", 0, 0], "original-row-physical-meaning-strict-1": [0, "b3c2aba3c1faf072e318feb7adb07f2b1d60970e4584354ef6584566e053d58e", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", 0, 0]}')
rejected = json.loads('[]')
assert jobs and all(stem.startswith("original-row-physical-meaning-") for stem in jobs)
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
assert len(strict_source.splitlines()) == source_lines <= 180
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
assert history == json.loads('{"artifacts": [{"bytes": 616, "path": "original-row-physical-meaning-audit-1.json", "sha256": "c51b00d3e0e6e640e6726bca0d59410d5513eed003adb1c8d3729c13d65fd97f"}, {"bytes": 90, "path": "original-row-physical-meaning-audit-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"bytes": 695, "path": "original-row-physical-meaning-audit-1.log", "sha256": "466693d2927694094f94b53a0c86ac875b0800da9109b6793c621acdc6d3a0f9"}, {"bytes": 114, "path": "original-row-physical-meaning-audit-1.usage.json", "sha256": "a31621f74e58f57c4ff5d9a685c80b55c57df5150a3f88ceb1157bbc5bb60600"}, {"bytes": 850, "path": "original-row-physical-meaning-public-1.json", "sha256": "60adaffa9365e9090bb24fa28d3b696df4ee310eb366ebb6d0cc06f2877a1b85"}, {"bytes": 90, "path": "original-row-physical-meaning-public-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"bytes": 431135, "path": "original-row-physical-meaning-public-1.log", "sha256": "4ec965e2d50131b88922ad5a3ca21d9a56212860c26474122f885e05b58ada4c"}, {"bytes": 6501, "path": "original-row-physical-meaning-public-1.source.lean", "sha256": "cfe7e86855615e4366e66954939927197483e04ce96a461ec89bd4abb434f328"}, {"bytes": 114, "path": "original-row-physical-meaning-public-1.usage.json", "sha256": "453257a0622a9587bd01ec8985d09afdb12483e8cc2b14118c56aad473df102b"}, {"bytes": 850, "path": "original-row-physical-meaning-strict-1.json", "sha256": "dd2a908574078415d7d3fb4e193df15e6d5184075272085dd1f6866b56719090"}, {"bytes": 90, "path": "original-row-physical-meaning-strict-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"bytes": 0, "path": "original-row-physical-meaning-strict-1.log", "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"}, {"bytes": 114, "path": "original-row-physical-meaning-strict-1.usage.json", "sha256": "fcd9afd13326bc648dcbe73314b37bf409548b107538a0fb252403b1b8f7c19b"}, {"bytes": 1108, "path": "root-source-precheck.json", "sha256": "d305fb7562d47b28efb8ba81e5c8981f6552cd50a7bb6a3965f78504d525b0f1"}, {"bytes": 501, "path": "signature-plan/context.lean.txt", "sha256": "e77baf30cd10e1d276341600663386d30104b8c05116ff77218b24257d0927e6"}, {"bytes": 457, "path": "signature-plan/private-signature.lean.txt", "sha256": "61c92c549e600f5ce9285a5d28908ffb0e20f6f88bab404b4aba3bad8aff44ef"}, {"bytes": 877, "path": "signature-plan/proposed-signature.lean.txt", "sha256": "5e1823c8064b825c21dbaf859381835154e19a231093e8f6e74f839bafb2f73c"}, {"bytes": 2846, "path": "source-proposal-audit/review.md", "sha256": "0c7d58a68a77b5f4e5ed8063cb052de7b87e2808556ecff1fb6cb85926d51020"}, {"bytes": 5083, "path": "source-proposal/source-addition.patch", "sha256": "794b089ae335215460c7c152f75043c015d8e38373e8be4563e1ac2b98c78c57"}], "patches": [], "rejected_public_types": [], "selected_source_sha256": "b3c2aba3c1faf072e318feb7adb07f2b1d60970e4584354ef6584566e053d58e", "status": "ROOT_ACCEPTED", "variants": [{"lines": 108, "path": "source-proposal/SourceCurrentOriginalRowPhysicalMeaning.lean", "sha256": "b3c2aba3c1faf072e318feb7adb07f2b1d60970e4584354ef6584566e053d58e"}, {"lines": 108, "path": "original-row-physical-meaning-strict-1.source.lean", "sha256": "b3c2aba3c1faf072e318feb7adb07f2b1d60970e4584354ef6584566e053d58e"}]}') and history["status"] == "ROOT_ACCEPTED"
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
        assert 0 < len(data.splitlines()) == item["lines"] <= 180
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
contracts = json.loads('{"context.lean.txt": {"path": "signature-plan/context.lean.txt", "lines": 9, "sha256": "e77baf30cd10e1d276341600663386d30104b8c05116ff77218b24257d0927e6"}, "private-signature.lean.txt": {"path": "signature-plan/private-signature.lean.txt", "lines": 8, "sha256": "61c92c549e600f5ce9285a5d28908ffb0e20f6f88bab404b4aba3bad8aff44ef"}, "proposed-signature.lean.txt": {"path": "signature-plan/proposed-signature.lean.txt", "lines": 16, "sha256": "5e1823c8064b825c21dbaf859381835154e19a231093e8f6e74f839bafb2f73c"}}')
required_contracts = {"context.lean.txt", "proposed-signature.lean.txt"}
assert required_contracts <= set(contracts) <= required_contracts | {"private-signature.lean.txt"}
expected_helpers = ["original_of_readback"] if "private-signature.lean.txt" in contracts else []
ordered_contracts = ["context.lean.txt"] + (["private-signature.lean.txt"] if expected_helpers else []) + ["proposed-signature.lean.txt"]
assert list(contracts) == ordered_contracts
positions = []
for filename, item in contracts.items():
    assert set(item) == {"path", "lines", "sha256"}
    relative = Path(item["path"])
    assert not relative.is_absolute() and ".." not in relative.parts
    declaration = (evidence / relative).read_bytes()
    assert re.fullmatch(r"[0-9a-f]{64}", item["sha256"]) and digest(declaration) == item["sha256"]
    assert type(item["lines"]) is int and 0 < len(declaration.splitlines()) == item["lines"] <= 180
    if filename == "context.lean.txt":
        assert source.startswith(declaration)
    else:
        literal = declaration.rstrip(b"\n") + b" := by\n"
        assert source.count(literal) == 1 and source.index(literal) >= len((evidence / contracts["context.lean.txt"]["path"]).read_bytes())
        positions.append(source.index(literal))
assert positions == sorted(positions) and len(set(positions)) == len(positions)
assert re.findall(r"^(?:private )?(?:noncomputable )?(?:def|theorem|lemma|abbrev|opaque|structure|inductive|instance) (\w+)", source.decode(), re.M) == expected_helpers + ["row_inputs_meaning"]
if args.live:
    assert (root / source_path).read_bytes() == source
original = (evidence / "original-sources/Audit.original.lean.txt").read_bytes()
assert digest(original) == "47087565238f473ef8269f9328bfe087f8902cd4976c18ce0aa5e6da39542308" and len(original.splitlines()) == 3123
assert load("original-source-index.json")["sources"] == [dict(path="lean/MicroCFTA/Audit.lean", snapshot="original-sources/Audit.original.lean.txt", lines=3123, sha256=digest(original))]
addition = b"import MicroCFTA.SourceCurrentOriginalRowPhysicalMeaning\n"
audit_source = (root / "lean/MicroCFTA/Audit.lean").read_bytes()
assert audit_source.count(addition) == 1 and audit_source.replace(addition, b"", 1) == original
assert audit_source.index(addition) < audit_source.index(b"/-!")
report = load("public-readback/original-row-physical-meaning-full-readback.json")
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
assert report["log_sha256"] == digest(raw) and report["log_bytes"] == len(raw) == int("431135")
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
assert checked.encode() == declared.encode() and len(checked) == int("8222") and len(checked.encode()) == int("8248")
assert len(checked.splitlines()) == int("112") and checked.count("\n") == int("111") and checked.endswith("\n") == json.loads('false')
assert digest(checked.encode()) == "a948f2dbd947fd8d7571b5810bf60e8ebcded9143866cb8b9dda68dca71de82b"
assert not any(token in checked for token in ["_private", "✝", "†", "‡"])
helpers = []
for line in source.decode().splitlines():
    if re.match(r"^\s*(?:(?:noncomputable|unsafe|partial)\s+)?private\b", line):
        declaration = re.match(r"^\s*(?:(?:noncomputable|unsafe|partial)\s+)?private\s+(?:(?:noncomputable|unsafe|partial)\s+)?(?:def|theorem|lemma|abbrev|opaque|instance|structure|inductive)\s+([^\s(\[{:=]+)", line)
        assert declaration, ("unsupported private declaration", line)
        helpers.append(declaration.group(1))
assert helpers == expected_helpers
assert not any(re.search(re.escape("MicroCFTA." + name + "." + helper) + r"(?![\w'])", checked) for helper in helpers)
head_report = report["heads"][0]
assert all(head_report[key] for key in ["check_print_type_identity", "check_print_type_byte_identity", "unique_complete_type_body_delimiter", "actual_axioms_within_standard_allowed"])
assert head_report["private_namespace_helpers_checked"] == helpers and head_report["private_type_spellings_checked"] == ["_private", "✝", "†", "‡"] and head_report["private_public_type_names"] is False
assert head_report["checked_type_characters"] == len(checked) and head_report["body_characters"] == len(body) == int("414058")
assert body.startswith("fun ") and len(body.encode()) == int("414346")
values = re.fullmatch(r"\s*\[([^\]]*)\]\s*", printed[axiom.end():]) if axiom.group(1) == "depends on axioms:" else None
assert values or (axiom.group(1) == "does not depend on any axioms" and not printed[axiom.end():].strip())
actual_axioms = {re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in values.group(1).split(",") if item.strip()} if values else set()
assert actual_axioms == set(head_report["actual_axioms"]) == set(json.loads('["Classical.choice", "Quot.sound", "propext"]')) and actual_axioms <= {"Classical.choice", "Quot.sound", "propext"}
for suffix, text in [("public-type", checked), ("printed-public-type", declared), ("body", body), ("axioms", axiom_output)]:
    filename = "original-row-physical-meaning-row_inputs_meaning-" + suffix + ".txt"
    retained = (evidence / "public-readback" / filename).read_bytes()
    assert retained == text.encode() and report["retained_slices"][filename] == dict(bytes=len(retained), sha256=digest(retained))
assert digest((evidence / "full-preparation/check-full-public.py").read_bytes()) == "ac93d3ac1442748997d75aced4777366bd891943fdc083aff6703bfbb9515436"
review = load("root-full-review.json")
assert review["status"] == "ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT" and review["source_sha256"] == selected_sha and review["source_lines"] == source_lines
assert review["public_theorem"] == head and review["complete_public_type_root_review"] == review["independent_complete_public_type_review"] == "CLEAR"
assert review["root_read_complete_public_type"] and review["root_printed_type_byte_identity_verified"] and review["check_print_type_byte_identity"] and review["four_private_markers_and_all_helpers_absent_from_type"]
assert review["type_sha256"] == digest(checked.encode()) and review["full_raw_sha256"] == digest(raw) and review["actual_axioms"] == sorted(actual_axioms)
assert review["body_retained_and_programmatically_checked"] and review["whole_body_manual_read_claimed"] is False
required_true = ['pure_original_admitted_row_physical_bridge', 'fixed_source_facts_holds_and_input_model', 'actual_original_available_closed_parent', 'literal_row_membership', 'children_original_and_admitted', 'all_ambient_row_language_equals_physical_edge_meaning', 'input_codec_order_preserved', 'no_state_or_resource_packet_needed']
required_false = ['execution_completion_claimed', 'scan_pruning_claimed', 'public_pass_claimed', 'haskell_refinement_claimed', 'whole_goal_complete', 'desired_semantic_law_premise', 'success_premise', 'fuel_premise', 'room_premise', 'state_or_rank_premise', 'canonical_model_replacement', 'silent_original_input_admission', 'generated_parent_oracle', 'mu_closed_body_inferred']
assert all(review[key] is True for key in required_true) and all(review[key] is False for key in required_false)
audit = (evidence / (audit_stem + ".log")).read_text()
build = re.search(r"Build completed successfully \((\d+) jobs\)\.", audit)
dependencies = re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", audit)
assert build and dependencies and not re.search(r"\berror(?:\([^)]*\))?:", audit)
assert int(build.group(1)) == int("3635") and int(dependencies.group(1)) == int("75453")
print(json.dumps(dict(status="PASS", live=args.live, **metrics, new_lean_lake_jobs=0, selected_modules=1, original_archives=1,
    audit_build_jobs=int(build.group(1)), audit_dependencies=int(dependencies.group(1)), audit_log_sha256=digest(audit.encode())), indent=2))
