"""Check saved same-symbol ready-comparison evidence. This script does not run Lean."""
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
evidence = root / "lean/restart-evidence/20261022-same-symbol-edge-ready"
def load(name):
    return json.loads((evidence / name).read_text())
def digest(data):
    return hashlib.sha256(data).hexdigest()
def undo(after, patch):
    lines, result, cursor, active = after.splitlines(keepends=True), [], 0, False
    for line in patch.splitlines(keepends=True):
        hunk = re.match(r"@@ -\d+(?:,\d+)? \+(\d+)(?:,\d+)? @@", line)
        if hunk:
            start = int(hunk.group(1)) - 1
            assert cursor <= start <= len(lines)
            result.extend(lines[cursor:start])
            cursor, active = start, True
        elif active:
            assert line[0] in " +-"
            if line[0] in " +":
                assert cursor < len(lines) and lines[cursor] == line[1:]
                cursor += 1
            if line[0] in " -":
                result.append(line[1:])
    assert active
    return "".join(result + lines[cursor:])

name, head = "SourceCurrentSameSymbolEdgeReady", "MicroCFTA.SourceCurrentSameSymbolEdgeReady.ready_complete"
selected_sha = "68d9ca87569a4bb4ad3d2df6e928c441a4e218bf54154c1da9f4d14de6b2c8aa"
jobs = {
    "same-symbol-edge-ready-strict-1": (1, "49443e0960e1229fe1fe855215b27ac75979aa7900adbeb4eca31ea69d9a2028", "d28eda9121db785045b347f5cc4b11c46e025525e9d3f0bf4deb753fa22b3063", 4, 0),
    "same-symbol-edge-ready-strict-2": (0, selected_sha, digest(b""), 0, 0),
    "same-symbol-edge-ready-public-1": (0, "c2d3fd4a25e6948363496d99e2ec309084319e8a69d7544ac3fddf56d28a66a2", "ffc63200806cbf19fa84666b5b288f39a6f40d8167bf7d886d143a97a7499dfe", 0, 0),
    "same-symbol-edge-ready-audit-1": (0, None, "18fafb8c4bb0d3de3e0c2b2f2adcbd433c1f3621f2035aaf79847fa80d113688", None, None),
}
assert (evidence / "same-symbol-edge-ready-audit-1.json").is_file(), "Audit is pending; no complete proof report is available"
actual = set()
for path in evidence.glob("*.json"):
    item = json.loads(path.read_text())
    if isinstance(item, dict) and "wrapper" in item and "exit_code" in item:
        if Path(item.get("command", [""])[0]).name in {"lean", "lake"}:
            actual.add(path.stem)
assert actual == set(jobs), actual
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
stricts = [(evidence / ("same-symbol-edge-ready-strict-" + str(i) + ".source.lean")).read_text() for i in [1, 2]]
assert [len(source.splitlines()) for source in stricts] == [191, 192]
assert undo(stricts[1], (evidence / "source-root-v2/unsupported-tactic.patch").read_text()) == stricts[0]
assert (evidence / "same-symbol-edge-ready-strict-2.log").read_bytes() == b""
selection = load("selected-sources.json")
source_path = "lean/MicroCFTA/" + name + ".lean"
assert selection == {source_path: dict(sha256=selected_sha, lines=192, strict="same-symbol-edge-ready-strict-2", full="same-symbol-edge-ready-public-1")}
source = (evidence / (name + ".lean")).read_bytes()
assert digest(source) == selected_sha and source.decode() == stricts[1]
gate = load("selected-source-gate.json")
assert gate == dict(status="ROOT_ACCEPTED", path=source_path, sha256=selected_sha, lines=192, snapshot="selected-sources/" + name + ".lean")
assert (evidence / gate["snapshot"]).read_bytes() == source
assert digest((evidence / "ready-plan/context.lean.txt").read_bytes()) == "6f0380cdad1a88b616f08fb963460edc6eb7e0e231372adc765f0f362dcc241b"
assert source.startswith((evidence / "ready-plan/context.lean.txt").read_bytes())
header = (evidence / "ready-plan/proposed-signature.lean.txt").read_bytes()
assert len(header.splitlines()) == 23 and digest(header) == "0e58683c1804a7193a2ede47a0600be1cd8ba73ca2a9338f82cb6725f9763e98" and source.count(header) == 1
if args.live:
    assert (root / source_path).read_bytes() == source
original = (evidence / "original-sources/Audit.original.lean.txt").read_bytes()
assert digest(original) == "a36b1f2aefc14b99db041f7b8c40c6c3acc79db4f563b87532fda88b24d392fc" and len(original.splitlines()) == 3115
assert load("original-source-index.json")["sources"] == [dict(path="lean/MicroCFTA/Audit.lean", snapshot="original-sources/Audit.original.lean.txt", lines=3115, sha256=digest(original))]
addition = b"import MicroCFTA.SourceCurrentSameSymbolEdgeReady\n"
audit_source = (root / "lean/MicroCFTA/Audit.lean").read_bytes()
assert audit_source.count(addition) == 1 and audit_source.replace(addition, b"", 1) == original
assert audit_source.index(addition) < audit_source.index(b"/-!")
report = load("public-readback/same-symbol-edge-ready-full-readback.json")
printer = (evidence / "same-symbol-edge-ready-public-1.source.lean").read_bytes()
raw = (evidence / "same-symbol-edge-ready-public-1.log").read_bytes()
options = ["maxRecDepth 30000", "maxHeartbeats 0", "linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true",
    "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]
tail = "\n" + "".join("set_option " + option + "\n" for option in options) + "".join(d + head + "\n" for d in ["#check @", "#print ", "#print axioms "])
assert printer == source + tail.encode() and len(printer.splitlines()) == 206 and len(tail.splitlines()) == 14
assert all(printer.decode().splitlines().count("set_option " + option) == 1 for option in options)
assert all(printer.decode().splitlines().count(d + head) == 1 for d in ["#check @", "#print ", "#print axioms "])
assert source.rstrip().endswith(("end MicroCFTA." + name).encode())
assert (report["source_sha256"], report["source_lines"], report["printer_sha256"]) == (selected_sha, 192, digest(printer))
assert report["log_sha256"] == digest(raw) and report["log_bytes"] == len(raw) == 1275208
assert report["receipt_sha256"] == digest((evidence / "same-symbol-edge-ready-public-1.json").read_bytes()) and report["owned_public_job_exit"] == 0
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
assert checked.encode() == declared.encode() and len(checked) == 21938 and len(checked.encode()) == 21954
assert len(checked.splitlines()) == 275 and checked.count("\n") == 274 and not checked.endswith("\n")
assert digest(checked.encode()) == "3318dd2a433532c6a7d313cf7b587303358e4f9092fe7d79523ef93ca6c44c69"
assert not any(token in checked for token in ["_private", "✝", "†", "‡"])
helpers = re.findall(r"^private (?:noncomputable )?(?:def|theorem|abbrev) (\w+)", source.decode(), re.M)
assert helpers == ["read_ready", "reverse_ready"]
assert not any(re.search(re.escape("MicroCFTA." + name + "." + helper) + r"(?![\w'])", checked) for helper in helpers)
head_report = report["heads"][0]
assert all(head_report[key] for key in ["check_print_type_identity", "check_print_type_byte_identity", "unique_complete_type_body_delimiter", "actual_axioms_within_standard_allowed"])
assert head_report["private_namespace_helpers_checked"] == helpers and head_report["private_type_spellings_checked"] == ["_private", "✝", "†", "‡"] and head_report["private_public_type_names"] is False
assert head_report["checked_type_characters"] == len(checked) and head_report["body_characters"] == len(body) == 1230987
assert body.startswith("fun ") and len(body.encode()) == 1231039
values = re.fullmatch(r"\s*\[([^\]]*)\]\s*", printed[axiom.end():]) if axiom.group(1) == "depends on axioms:" else None
assert values or (axiom.group(1) == "does not depend on any axioms" and not printed[axiom.end():].strip())
actual_axioms = {re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in values.group(1).split(",") if item.strip()} if values else set()
assert actual_axioms == set(head_report["actual_axioms"]) and actual_axioms <= {"Classical.choice", "Quot.sound", "propext"}
for suffix, text in [("public-type", checked), ("printed-public-type", declared), ("body", body), ("axioms", axiom_output)]:
    filename = "same-symbol-edge-ready-ready_complete-" + suffix + ".txt"
    retained = (evidence / "public-readback" / filename).read_bytes()
    assert retained == text.encode() and report["retained_slices"][filename] == dict(bytes=len(retained), sha256=digest(retained))
assert digest((evidence / "full-preparation/check-full-public.py").read_bytes()) == "2505e30bba74438e1f3ca76fd3f5efe7059437a3e2145e2749fd6fbbf1384b59"
review = load("root-full-review.json")
assert review["status"] == "ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT" and review["source_sha256"] == selected_sha and review["source_lines"] == 192
assert review["public_theorem"] == head and review["complete_public_type_root_review"] == review["independent_complete_public_type_review"] == "CLEAR"
assert review["root_read_both_complete_type_files"] and review["check_print_type_byte_identity"] and review["four_private_markers_and_all_helpers_absent_from_type"]
assert review["type_sha256"] == digest(checked.encode()) and review["full_raw_sha256"] == digest(raw) and review["actual_axioms"] == sorted(actual_axioms)
assert review["body_retained_and_programmatically_checked"] and review["whole_body_manual_read_claimed"] is False
assert review["execution_and_result_law_derived"] and review["entire_checked_state_unchanged"] and review["native_execution_or_result_law_premise"] is False
audit = (evidence / "same-symbol-edge-ready-audit-1.log").read_text()
build = re.search(r"Build completed successfully \((\d+) jobs\)\.", audit)
dependencies = re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", audit)
assert build and dependencies and not re.search(r"\berror(?:\([^)]*\))?:", audit)
assert int(build.group(1)) == 3627 and int(dependencies.group(1)) == 75377
print(json.dumps(dict(status="PASS", live=args.live, source_jobs=3, audit_jobs=1, actual_jobs=4,
    failed_jobs=1, warned_source_exit_zero_jobs=0, rejected_public_type_jobs=0, new_lean_lake_jobs=0, selected_modules=1, original_archives=1,
    audit_build_jobs=int(build.group(1)), audit_dependencies=int(dependencies.group(1)), audit_log_sha256=digest(audit.encode())), indent=2))
