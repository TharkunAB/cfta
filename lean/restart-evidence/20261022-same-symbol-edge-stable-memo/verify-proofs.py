"""Check saved same-symbol stable-memo evidence. This script does not run Lean."""
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
evidence = root / "lean/restart-evidence/20261022-same-symbol-edge-stable-memo"
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

name, head = "SourceCurrentSameSymbolEdgeStable", "MicroCFTA.SourceCurrentSameSymbolEdgeStable.completed_preserves"
selected_sha = "6c96e7e8d5cb32d1209818ed65de83a5104b6a409d65b9caffb52d802e874b91"
jobs = {
    "same-symbol-edge-stable-strict-1": (1, "c2fd48c1cc5358f9a3efd1e19096ec1c6333ae14b3c9414dc530409d9ed6b339", "e3f91778d1bd3b0e7cd4e22511f42d00452583bff691fabeed71966ed9397c58", 10, 17),
    "same-symbol-edge-stable-strict-2": (1, "35a92ce3bd517baeeccf0df68acf5ed1c7f87eb98e351f59b649cf5fa6777e7b", "363236103f7ebe9d5efdce63155e0114c891c84fc2e6c8d43dfd3cc3a762118a", 4, 2),
    "same-symbol-edge-stable-strict-3": (0, "f665ea5c2b6a36cd583796b87e51b563106a5c536a9274cfbe7b633b6d05dc93", "e10faddc5a717142ebcaaa31754197c51bc6d07eabb54af65ca12eb0d1cc444c", 0, 1),
    "same-symbol-edge-stable-strict-4": (0, selected_sha, digest(b""), 0, 0),
    "same-symbol-edge-stable-public-1": (0, "bdfef58f4970665cb953b00d137a040be4272d88399ef85832060193b766aba3", "d3c35861e47b59aa58b4ee16a68b756c8d6cae70037fcf9292677486f79b0050", 0, 0),
    "same-symbol-edge-stable-audit-1": (0, None, "c4b5c7f777ec5c09154b2a0fb383b9b7686aa6a9f0370a7ef272b4739fe8fab9", None, None),
}
assert (evidence / "same-symbol-edge-stable-audit-1.json").is_file(), "Audit is pending; no complete proof report is available"
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
stricts = [(evidence / ("same-symbol-edge-stable-strict-" + str(i) + ".source.lean")).read_text() for i in [1, 2, 3, 4]]
assert [len(source.splitlines()) for source in stricts] == [312, 329, 338, 338]
assert undo(stricts[1], (evidence / "source-author-v3/strict-1-repair.patch").read_text()) == stricts[0]
assert undo(stricts[2], (evidence / "source-root-v4/sequenced-rewrite.patch").read_text()) == stricts[1]
assert undo(stricts[3], (evidence / "source-root-v5/unused-argument.patch").read_text()) == stricts[2]
assert (evidence / "same-symbol-edge-stable-strict-4.log").read_bytes() == b""
selection = load("selected-sources.json")
source_path = "lean/MicroCFTA/" + name + ".lean"
assert selection == {source_path: dict(sha256=selected_sha, lines=338, strict="same-symbol-edge-stable-strict-4", full="same-symbol-edge-stable-public-1")}
source = (evidence / (name + ".lean")).read_bytes()
assert digest(source) == selected_sha and source.decode() == stricts[3]
gate = load("selected-source-gate.json")
assert gate == dict(status="ROOT_ACCEPTED", path=source_path, sha256=selected_sha, lines=338, snapshot="selected-sources/" + name + ".lean")
assert (evidence / gate["snapshot"]).read_bytes() == source
assert digest((evidence / "stable-plan/context.lean.txt").read_bytes()) == "98865794f3b88d7af726534efddb9f764c8adbf9ec27b6db0d93d30fc8d4441c"
assert source.startswith((evidence / "stable-plan/context.lean.txt").read_bytes())
header = (evidence / "stable-plan/proposed-signature.lean.txt").read_bytes()
assert len(header.splitlines()) == 19 and digest(header) == "78568f85e42a1d445a3b0ab2c6c01d24964837b496a0ed2b2a8b5845207d1001" and source.count(header) == 1
stable = b"".join(source.splitlines(keepends=True)[13:37])
assert len(stable.splitlines()) == 24 and digest(stable) == "ba6a5f925d1a96cb20435e3d64c62678a61bdc5a4acd103002d9d051a06cac81"
if args.live:
    assert (root / source_path).read_bytes() == source
original = (evidence / "original-sources/Audit.original.lean.txt").read_bytes()
assert digest(original) == "1d082f8610403a8c0fd6f11848020f915ff04f5bf7e60f72ba4bc3615041f5f6" and len(original.splitlines()) == 3114
assert load("original-source-index.json")["sources"] == [dict(path="lean/MicroCFTA/Audit.lean", snapshot="original-sources/Audit.original.lean.txt", lines=3114, sha256=digest(original))]
addition = b"import MicroCFTA.SourceCurrentSameSymbolEdgeStable\n"
audit_source = (root / "lean/MicroCFTA/Audit.lean").read_bytes()
assert audit_source.count(addition) == 1 and audit_source.replace(addition, b"", 1) == original
assert audit_source.index(addition) < audit_source.index(b"/-!")
report = load("public-readback/same-symbol-edge-stable-full-readback.json")
printer = (evidence / "same-symbol-edge-stable-public-1.source.lean").read_bytes()
raw = (evidence / "same-symbol-edge-stable-public-1.log").read_bytes()
options = ["maxRecDepth 30000", "maxHeartbeats 0", "linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true",
    "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]
tail = "\n" + "".join("set_option " + option + "\n" for option in options) + "".join(d + head + "\n" for d in ["#check @", "#print ", "#print axioms "])
assert printer == source + tail.encode() and len(printer.splitlines()) == 352 and len(tail.splitlines()) == 14
assert all(printer.decode().splitlines().count("set_option " + option) == 1 for option in options)
assert all(printer.decode().splitlines().count(d + head) == 1 for d in ["#check @", "#print ", "#print axioms "])
assert source.rstrip().endswith(("end MicroCFTA." + name).encode())
assert (report["source_sha256"], report["source_lines"], report["printer_sha256"]) == (selected_sha, 338, digest(printer))
assert report["log_sha256"] == digest(raw) and report["log_bytes"] == len(raw) == 4469864
assert report["receipt_sha256"] == digest((evidence / "same-symbol-edge-stable-public-1.json").read_bytes()) and report["owned_public_job_exit"] == 0
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
assert checked.encode() == declared.encode() and len(checked) == 15394 and len(checked.encode()) == 15414
assert len(checked.splitlines()) == 201 and checked.count("\n") == 200 and not checked.endswith("\n")
assert digest(checked.encode()) == "b77d5025ebff2218f5a4214cfe0027434320a0fd1d10868c5f8602c23a684259"
assert not any(token in checked for token in ["_private", "✝", "†", "‡"])
helpers = re.findall(r"^private (?:noncomputable )?(?:def|theorem|abbrev) (\w+)", source.decode(), re.M)
assert helpers == ["Memo", "key", "started", "written", "tail_done", "ret_memo", "native_memo", "overwrite_cells", "miss_order", "ready_cell", "finish_started", "finish_two", "call_image", "written_fields"]
assert not any(re.search(re.escape("MicroCFTA." + name + "." + helper) + r"(?![\w'])", checked) for helper in helpers)
head_report = report["heads"][0]
assert all(head_report[key] for key in ["check_print_type_identity", "check_print_type_byte_identity", "unique_complete_type_body_delimiter", "actual_axioms_within_standard_allowed"])
assert head_report["private_namespace_helpers_checked"] == helpers and head_report["private_type_spellings_checked"] == ["_private", "✝", "†", "‡"] and head_report["private_public_type_names"] is False
assert head_report["checked_type_characters"] == len(checked) and head_report["body_characters"] == len(body) == 4438655
assert body.startswith("fun ") and len(body.encode()) == 4438757
values = re.fullmatch(r"\s*\[([^\]]*)\]\s*", printed[axiom.end():]) if axiom.group(1) == "depends on axioms:" else None
assert values or (axiom.group(1) == "does not depend on any axioms" and not printed[axiom.end():].strip())
actual_axioms = {re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in values.group(1).split(",") if item.strip()} if values else set()
assert actual_axioms == set(head_report["actual_axioms"]) and actual_axioms <= {"Classical.choice", "Quot.sound", "propext"}
for suffix, text in [("public-type", checked), ("printed-public-type", declared), ("body", body), ("axioms", axiom_output)]:
    filename = "same-symbol-edge-stable-completed_preserves-" + suffix + ".txt"
    retained = (evidence / "public-readback" / filename).read_bytes()
    assert retained == text.encode() and report["retained_slices"][filename] == dict(bytes=len(retained), sha256=digest(retained))
assert digest((evidence / "full-preparation/check-full-public.py").read_bytes()) == "745e6d3da68968fcbe715eb5a84bdeeb83a5342a321b1ea1746c19dbd31995c3"
review = load("root-full-review.json")
assert review["status"] == "ROOT_ACCEPTED_FOR_OFFICIAL_INSTALL_AND_AUDIT" and review["source_sha256"] == selected_sha and review["source_lines"] == 338
assert review["public_theorem"] == head and review["complete_public_type_root_review"] == review["independent_complete_public_type_review"] == "CLEAR"
assert review["root_read_both_complete_type_files"] and review["check_print_type_byte_identity"] and review["four_private_markers_and_all_helpers_absent_from_type"]
assert review["type_sha256"] == digest(checked.encode()) and review["full_raw_sha256"] == digest(raw) and review["actual_axioms"] == sorted(actual_axioms)
assert review["body_retained_and_programmatically_checked"] and review["whole_body_manual_read_claimed"] is False
audit = (evidence / "same-symbol-edge-stable-audit-1.log").read_text()
build = re.search(r"Build completed successfully \((\d+) jobs\)\.", audit)
dependencies = re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", audit)
assert build and dependencies and not re.search(r"\berror(?:\([^)]*\))?:", audit)
assert int(build.group(1)) == 3626 and int(dependencies.group(1)) == 75371
print(json.dumps(dict(status="PASS", live=args.live, source_jobs=5, audit_jobs=1, actual_jobs=6,
    failed_jobs=2, warned_source_exit_zero_jobs=1, rejected_public_type_jobs=0, new_lean_lake_jobs=0, selected_modules=1, original_archives=1,
    audit_build_jobs=int(build.group(1)), audit_dependencies=int(dependencies.group(1)), audit_log_sha256=digest(audit.encode())), indent=2))
