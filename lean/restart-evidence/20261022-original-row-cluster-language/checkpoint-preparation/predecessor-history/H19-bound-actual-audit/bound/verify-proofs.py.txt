"""Check saved original-row deletion-soundness evidence. This script does not run Lean."""
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
evidence = root / "lean/restart-evidence/20261022-original-row-deletion-soundness"
def load(name):
    return json.loads((evidence / name).read_text())
def digest(data):
    return hashlib.sha256(data).hexdigest()
name, head = "SourceCurrentOriginalRowDeletionSoundness", "MicroCFTA.SourceCurrentOriginalRowDeletionSoundness.deletion_sound"
selected_sha = "a4dd0cdd8a73cdd0e0a87f4ef668f9708cbee9b9132108424411772a8c91ae0a"
source_lines = int("105")
strict_stem, full_stem, audit_stem = "original-row-deletion-soundness-strict-1", "original-row-deletion-soundness-public-1", "original-row-deletion-soundness-audit-1"
metrics = dict(actual_jobs=int("3"), source_jobs=int("2"), audit_jobs=int("1"),
    failed_jobs=int("0"), warned_source_exit_zero_jobs=int("0"),
    rejected_public_type_jobs=int("0"))
jobs = json.loads('{"original-row-deletion-soundness-audit-1": [0, null, "da1e97ab1910308be353811d334d4f294181e7f7ab8f0f7567716fd6231f0616", 0, 0], "original-row-deletion-soundness-public-1": [0, "8155393648ebccd6be20d6efcdd43588363cb0e701de4fc6854bbce7acc31453", "b754194bf85bd6c73e6dae7eef38f0563fa43e69c2b5aff5317e5a859f4c3457", 0, 0], "original-row-deletion-soundness-strict-1": [0, "a4dd0cdd8a73cdd0e0a87f4ef668f9708cbee9b9132108424411772a8c91ae0a", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855", 0, 0]}')
rejected = json.loads('[]')
assert jobs and all(stem.startswith("original-row-deletion-soundness-") for stem in jobs)
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
assert history == json.loads('{"artifacts": [{"bytes": 622, "path": "original-row-deletion-soundness-audit-1.json", "sha256": "2ff432d70f138532445da1a54f152dfc9db95d17ffaa1e4745460c11607c827c"}, {"bytes": 90, "path": "original-row-deletion-soundness-audit-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"bytes": 697, "path": "original-row-deletion-soundness-audit-1.log", "sha256": "da1e97ab1910308be353811d334d4f294181e7f7ab8f0f7567716fd6231f0616"}, {"bytes": 114, "path": "original-row-deletion-soundness-audit-1.usage.json", "sha256": "418d9eea6dc0fe927abc6f6a64bf725414689ec25bbf5b9571b71b23215e5faa"}, {"bytes": 862, "path": "original-row-deletion-soundness-public-1.json", "sha256": "15b8a0bde309fe88eec0bc7f8ef5779b35968bb9cdad82fc602f9600cd6fad89"}, {"bytes": 90, "path": "original-row-deletion-soundness-public-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"bytes": 250381, "path": "original-row-deletion-soundness-public-1.log", "sha256": "b754194bf85bd6c73e6dae7eef38f0563fa43e69c2b5aff5317e5a859f4c3457"}, {"bytes": 6461, "path": "original-row-deletion-soundness-public-1.source.lean", "sha256": "8155393648ebccd6be20d6efcdd43588363cb0e701de4fc6854bbce7acc31453"}, {"bytes": 114, "path": "original-row-deletion-soundness-public-1.usage.json", "sha256": "a6455b958cddd02e13bf2154e38d05a8748a7c83b242a0a48b8b3619de8703cf"}, {"bytes": 862, "path": "original-row-deletion-soundness-strict-1.json", "sha256": "b5b17922e211fef758c3f4238a3153e07325ed1c0f997f2a683739f7542db85d"}, {"bytes": 90, "path": "original-row-deletion-soundness-strict-1.limits.json", "sha256": "408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3"}, {"bytes": 0, "path": "original-row-deletion-soundness-strict-1.log", "sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"}, {"bytes": 114, "path": "original-row-deletion-soundness-strict-1.usage.json", "sha256": "ab340737a308cea843cc80a2d44abb590d1d58010f303af1c45e7401172b141e"}, {"bytes": 1428, "path": "root-source-precheck.json", "sha256": "d21fcf2c48ead5368ab8621c713c557bbf242aa21115b18bd737815311446cdf"}, {"bytes": 464, "path": "signature-plan/context.lean.txt", "sha256": "afe61fd9ff562d6b562bd7ccb2053afdd1528ac2711236a7d6447567034d2928"}, {"bytes": 1869, "path": "signature-plan/proposed-signature.lean.txt", "sha256": "fcf8cfe500c226bce7eca1c4a3f8475b49f39d5fb798ff7c795094fa9ad90426"}, {"bytes": 2517, "path": "source-proposal-audit/review.md", "sha256": "4f3cb78bd21d633bad8dab315fc1b7932b5807a8fb908cf003df057f4af85bc1"}, {"bytes": 4090, "path": "source-proposal/source-addition.patch", "sha256": "3d94a7c9d45ef475a799683a4cdfb4deac2cabe644145702f6868abf3afbf5cb"}], "patches": [], "rejected_public_types": [], "selected_source_sha256": "a4dd0cdd8a73cdd0e0a87f4ef668f9708cbee9b9132108424411772a8c91ae0a", "status": "ROOT_ACCEPTED", "variants": [{"lines": 105, "path": "source-proposal/SourceCurrentOriginalRowDeletionSoundness.lean", "sha256": "a4dd0cdd8a73cdd0e0a87f4ef668f9708cbee9b9132108424411772a8c91ae0a"}, {"lines": 105, "path": "original-row-deletion-soundness-strict-1.source.lean", "sha256": "a4dd0cdd8a73cdd0e0a87f4ef668f9708cbee9b9132108424411772a8c91ae0a"}]}') and history["status"] == "ROOT_ACCEPTED"
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
contracts = json.loads('{"context.lean.txt": {"path": "signature-plan/context.lean.txt", "lines": 8, "sha256": "afe61fd9ff562d6b562bd7ccb2053afdd1528ac2711236a7d6447567034d2928"}, "proposed-signature.lean.txt": {"path": "signature-plan/proposed-signature.lean.txt", "lines": 36, "sha256": "fcf8cfe500c226bce7eca1c4a3f8475b49f39d5fb798ff7c795094fa9ad90426"}}')
required_contracts = {"context.lean.txt", "proposed-signature.lean.txt"}
assert required_contracts <= set(contracts) <= required_contracts | {"private-signature.lean.txt"}
expected_helpers = ["canonical_sound"] if "private-signature.lean.txt" in contracts else []
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
assert re.findall(r"^(?:private )?(?:noncomputable )?(?:def|theorem|lemma|abbrev|opaque|structure|inductive|instance) (\w+)", source.decode(), re.M) == expected_helpers + ["deletion_sound"]
if args.live:
    assert (root / source_path).read_bytes() == source
original = (evidence / "original-sources/Audit.original.lean.txt").read_bytes()
assert digest(original) == "3dcbcdcec1ff02d14f17784dda3eba709811d291e1c82619d5eb1b4fac4ecd4e" and len(original.splitlines()) == 3124
assert load("original-source-index.json")["sources"] == [dict(path="lean/MicroCFTA/Audit.lean", snapshot="original-sources/Audit.original.lean.txt", lines=3124, sha256=digest(original))]
addition = b"import MicroCFTA.SourceCurrentOriginalRowDeletionSoundness\n"
audit_source = (root / "lean/MicroCFTA/Audit.lean").read_bytes()
assert audit_source.count(addition) == 1 and audit_source.replace(addition, b"", 1) == original
assert audit_source.index(addition) < audit_source.index(b"/-!")
report = load("public-readback/original-row-deletion-soundness-full-readback.json")
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
assert report["log_sha256"] == digest(raw) and report["log_bytes"] == len(raw) == int("250381")
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
assert checked.encode() == declared.encode() and len(checked) == int("21211") and len(checked.encode()) == int("21255")
assert len(checked.splitlines()) == int("256") and checked.count("\n") == int("255") and checked.endswith("\n") == json.loads('false')
assert digest(checked.encode()) == "b83d40149dd1db19b919413d5eca5a5177e0f99fec652f800444a61f535462b5"
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
assert head_report["checked_type_characters"] == len(checked) and head_report["body_characters"] == len(body) == int("207524")
assert body.startswith("fun ") and len(body.encode()) == int("207584")
values = re.fullmatch(r"\s*\[([^\]]*)\]\s*", printed[axiom.end():]) if axiom.group(1) == "depends on axioms:" else None
assert values or (axiom.group(1) == "does not depend on any axioms" and not printed[axiom.end():].strip())
actual_axioms = {re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in values.group(1).split(",") if item.strip()} if values else set()
assert actual_axioms == set(head_report["actual_axioms"]) == set(json.loads('["Classical.choice", "Quot.sound", "propext"]')) and actual_axioms <= {"Classical.choice", "Quot.sound", "propext"}
for suffix, text in [("public-type", checked), ("printed-public-type", declared), ("body", body), ("axioms", axiom_output)]:
    filename = "original-row-deletion-soundness-deletion_sound-" + suffix + ".txt"
    retained = (evidence / "public-readback" / filename).read_bytes()
    assert retained == text.encode() and report["retained_slices"][filename] == dict(bytes=len(retained), sha256=digest(retained))
assert digest((evidence / "full-preparation/check-full-public.py").read_bytes()) == "5b6de82fb62cad65f417ba1fd586b34382100439fef2ef572cd53ce3b105f7a4"
review = load("root-full-review.json")
assert review["status"] == "ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT" and review["source_sha256"] == selected_sha and review["source_lines"] == source_lines
assert review["public_theorem"] == head and review["complete_public_type_root_review"] == review["independent_complete_public_type_review"] == "CLEAR"
assert review["root_read_complete_public_type"] and review["root_printed_type_byte_identity_verified"] and review["check_print_type_byte_identity"] and review["four_private_markers_and_all_helpers_absent_from_type"]
assert review["type_sha256"] == digest(checked.encode()) and review["full_raw_sha256"] == digest(raw) and review["actual_axioms"] == sorted(actual_axioms)
assert review["body_retained_and_programmatically_checked"] and review["whole_body_manual_read_claimed"] is False
required_true = ['pure_completed_result_identity_deletion_inclusions', 'both_physical_inclusions_for_every_ambient', 'fixed_source_facts_holds_model_and_ranked_input', 'actual_original_available_closed_parent', 'same_model_parent_admission_explicit', 'two_literal_original_row_memberships', 'same_completed_h15_common_edge_and_final_heap', 'final_coherence_growth_and_result_residency_explicit', 'canonical_empty_domain_edge_law_explicit_completed_past_argument', 'edge_law_includes_sound_and_complete', 'ranked_input_indexes_existing_edge_law', 'h18_original_admitted_children_and_physical_row_bridge', 'edge_law_sound_projection_only', 'identity_to_complete_payload_equality_derived', 'canonical_order_swaps_only_conjunction']
required_false = ['new_operational_completion_claimed', 'new_resource_producer_claimed', 'scan_language_preservation_claimed', 'public_pass_claimed', 'haskell_refinement_claimed', 'whole_goal_complete', 'new_comparison_execution_premise', 'room_or_width_premise', 'total_exact_meet_oracle', 'fresh_semantic_law_producer_claimed', 'bounded_completeness_projection_used', 'rank_erasure_used', 'canonical_model_replacement', 'silent_original_input_admission', 'generated_parent_oracle', 'mu_closed_body_inferred']
assert all(review[key] is True for key in required_true) and all(review[key] is False for key in required_false)
audit = (evidence / (audit_stem + ".log")).read_text()
build = re.search(r"Build completed successfully \((\d+) jobs\)\.", audit)
dependencies = re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", audit)
assert build and dependencies and not re.search(r"\berror(?:\([^)]*\))?:", audit)
assert int(build.group(1)) == int("3636") and int(dependencies.group(1)) == int("75454")
print(json.dumps(dict(status="PASS", live=args.live, **metrics, new_lean_lake_jobs=0, selected_modules=1, original_archives=1,
    audit_build_jobs=int(build.group(1)), audit_dependencies=int(dependencies.group(1)), audit_log_sha256=digest(audit.encode())), indent=2))
