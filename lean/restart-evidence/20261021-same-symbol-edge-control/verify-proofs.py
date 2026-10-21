"""Check saved same-symbol control evidence. This script does not run Lean."""
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
evidence = root / "lean/restart-evidence/20261021-same-symbol-edge-control"
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

name, head = "SourceCurrentSameSymbolEdgeControl", "MicroCFTA.SourceCurrentSameSymbolEdgeControl.miss_readback"
selected_sha = "dbf416168635ecc34effe17891f557f31ec14df2f7cb368c52863d69a6174559"
jobs = {
    "same-symbol-edge-strict-1": (1, "89ceb64ea5bc18f5a2c712a8764e345398344113519ec7d6516724847e17bb6a", "1e8850864aef836a8525a156f79e61577b4fd8dc4f1b804bbd50dc03076111cd", 6, 2),
    "same-symbol-edge-strict-2": (0, "062815f1619dce95fac323ce8bfdaebdf11252728516503d6e9ac3c87b034141", "8d2ec6755ee878cdc3e2637b158dd50684dc193ff81a4ad498234e28bc45bdd3", 0, 1),
    "same-symbol-edge-strict-3": (0, selected_sha, digest(b""), 0, 0),
    "same-symbol-edge-public-1": (0, "75b3982bc568afb39dfdc91cf0f1f5ab3c38fcbfcfb5669c3355d6a15c5b3995", "e90cfe4417e4cc5fec32da1dec6cae89d9ce3b31ef6b6a32fd61a1dfc0571bb6", 0, 0),
    "same-symbol-edge-audit-1": (0, None, "4e6d8db305002d56aa075782fee1591b65490e4db1aba48bd9006a37d249de18", None, None),
}
assert (evidence / "same-symbol-edge-audit-1.json").is_file(), "Audit is pending; no complete proof report is available"
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
stricts = [(evidence / ("same-symbol-edge-strict-" + str(i) + ".source.lean")).read_text() for i in [1, 2, 3]]
assert [len(source.splitlines()) for source in stricts] == [330, 334, 334]
assert undo(stricts[1], (evidence / "control-strict-repair-v4/proof-only.patch").read_text()) == stricts[0]
assert undo(stricts[2], (evidence / "control-warning-repair-v5/deprecation-only.patch").read_text()) == stricts[1]
assert "`if_neg` has been deprecated" in (evidence / "same-symbol-edge-strict-2.log").read_text()
assert (evidence / "same-symbol-edge-strict-3.log").read_bytes() == b""
selection = load("selected-sources.json")
source_path = "lean/MicroCFTA/" + name + ".lean"
assert selection == {source_path: dict(sha256=selected_sha, lines=334, strict="same-symbol-edge-strict-3", full="same-symbol-edge-public-1")}
source = (evidence / (name + ".lean")).read_bytes()
assert digest(source) == selected_sha and source.decode() == stricts[2]
if args.live:
    assert (root / source_path).read_bytes() == source
original = (evidence / "original-sources/Audit.original.lean.txt").read_bytes()
assert digest(original) == "54c43b5a02ca28f66963385976ae3e3846d903b5294d9ecca7dc476d5c137901" and len(original.splitlines()) == 3112
assert load("original-source-index.json")["sources"] == [dict(path="lean/MicroCFTA/Audit.lean", snapshot="original-sources/Audit.original.lean.txt", lines=3112, sha256=digest(original))]
addition = b"import MicroCFTA.SourceCurrentSameSymbolEdgeControl\n"
audit_source = (root / "lean/MicroCFTA/Audit.lean").read_bytes()
assert audit_source.count(addition) == 1 and audit_source.replace(addition, b"", 1) == original
assert audit_source.index(addition) < audit_source.index(b"/-!")
report = load("public-readback/same-symbol-edge-full-readback.json")
printer = (evidence / "same-symbol-edge-public-1.source.lean").read_bytes()
raw = (evidence / "same-symbol-edge-public-1.log").read_bytes()
options = ["maxRecDepth 30000", "maxHeartbeats 0", "linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true",
    "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]
tail = "\n" + "".join("set_option " + option + "\n" for option in options) + "".join(d + head + "\n" for d in ["#check @", "#print ", "#print axioms "])
assert printer == source + tail.encode() and len(printer.splitlines()) == 348 and len(tail.splitlines()) == 14
assert all(printer.decode().splitlines().count("set_option " + option) == 1 for option in options)
assert all(printer.decode().splitlines().count(d + head) == 1 for d in ["#check @", "#print ", "#print axioms "])
assert source.rstrip().endswith(("end MicroCFTA." + name).encode())
assert (report["source_sha256"], report["source_lines"], report["printer_sha256"]) == (selected_sha, 334, digest(printer))
assert report["log_sha256"] == digest(raw) and report["log_bytes"] == len(raw) == 6247397
assert report["receipt_sha256"] == digest((evidence / "same-symbol-edge-public-1.json").read_bytes()) and report["owned_public_job_exit"] == 0
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
assert checked.encode() == declared.encode() and len(checked) == 34814 and len(checked.encode()) == 34826
assert len(checked.splitlines()) == 449 and checked.count("\n") == 448 and not checked.endswith("\n")
assert digest(checked.encode()) == "a08d7f8d6b6082591a6ebdf83a77d40507f59c1227034dcd83ae933976767206"
assert not any(token in checked for token in ["_private", "✝", "†", "‡"])
helpers = re.findall(r"^private (?:noncomputable )?(?:def|theorem|abbrev) (\w+)", source.decode(), re.M)
assert helpers == ["Memo", "pairKey", "MemoValid", "tail_done", "finish_table", "ret_done", "native_done", "start_miss"]
assert not any(re.search(re.escape("MicroCFTA." + name + "." + helper) + r"(?![\w'])", checked) for helper in helpers)
head_report = report["heads"][0]
assert all(head_report[key] for key in ["check_print_type_identity", "check_print_type_byte_identity", "unique_complete_type_body_delimiter", "actual_axioms_within_standard_allowed"])
assert head_report["private_namespace_helpers_checked"] == helpers and head_report["private_type_spellings_checked"] == ["_private", "✝", "†", "‡"] and head_report["private_public_type_names"] is False
assert head_report["checked_type_characters"] == len(checked) and head_report["body_characters"] == len(body) == 6177217
assert body.startswith("fun ") and len(body.encode()) == 6177481
values = re.fullmatch(r"\s*\[([^\]]*)\]\s*", printed[axiom.end():]) if axiom.group(1) == "depends on axioms:" else None
assert values or (axiom.group(1) == "does not depend on any axioms" and not printed[axiom.end():].strip())
actual_axioms = {re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in values.group(1).split(",") if item.strip()} if values else set()
assert actual_axioms == set(head_report["actual_axioms"]) and actual_axioms <= {"Classical.choice", "Quot.sound", "propext"}
for suffix, text in [("public-type", checked), ("printed-public-type", declared), ("body", body), ("axioms", axiom_output)]:
    filename = "same-symbol-edge-miss_readback-" + suffix + ".txt"
    retained = (evidence / "public-readback" / filename).read_bytes()
    assert retained == text.encode() and report["retained_slices"][filename] == dict(bytes=len(retained), sha256=digest(retained))
assert digest((evidence / "full-preparation/same-symbol-edge-check-full-public.py").read_bytes()) == "2fb41230e26984fa584bf1b34a2725d0cd20f92710a38998f8bf183104e61e49"
audit = (evidence / "same-symbol-edge-audit-1.log").read_text()
build = re.search(r"Build completed successfully \((\d+) jobs\)\.", audit)
dependencies = re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", audit)
assert build and dependencies and not re.search(r"\berror(?:\([^)]*\))?:", audit)
assert int(build.group(1)) == 3624 and int(dependencies.group(1)) == 75337
print(json.dumps(dict(status="PASS", live=args.live, source_jobs=4, audit_jobs=1, actual_jobs=5,
    failed_jobs=1, warned_source_exit_zero_jobs=1, rejected_public_type_jobs=0, new_lean_lake_jobs=0, selected_modules=1, original_archives=1,
    audit_build_jobs=int(build.group(1)), audit_dependencies=int(dependencies.group(1)), audit_log_sha256=digest(audit.encode())), indent=2))
