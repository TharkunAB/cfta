"""Check saved finite warm-call proof evidence. This script does not run Lean."""
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
evidence = root / "lean/restart-evidence/20261021-finite-warm-calls"
def load(name):
    return json.loads((evidence / name).read_text())
def digest(data):
    return hashlib.sha256(data).hexdigest()

selected = {
    "SourceCurrentFiniteWarmCalls": ("984f34529a1050fd015ba0fb742b39cc38e0b518eaae69801cbde1727578a6bd", 236, "finite-calls-strict-3", "finite-calls-public-1"),
}
original = {
    "Audit": ("1013bd1cb1c723049d249b7940b57569cb1c19824b89fae206708db1a4732a11", 3110),
}
jobs = {
    "finite-calls-strict-1": (1, "32cfa9e1a229237dcaf683fe77f588cb2eeb541929f7e4dff33ef2809370183c", "536c7dcafa80eb9be2e5d2f72aa1b4da3c37e35310b876f90ccb2adc70f586fb"),
    "finite-calls-strict-2": (0, "84e7803898495e956335917802621bb616585f3ff223274809c3eba182c431cc", "2bfc91f812da7bd2819ca50acd9d1c54ceeffc3471579920b8de26edd7cc085b"),
    "finite-calls-strict-3": (0, selected["SourceCurrentFiniteWarmCalls"][0], hashlib.sha256(b"").hexdigest()),
    "finite-calls-public-1": (0, "cbea63ae250f1fc671c8ade3c30801d523cc757c2d375b8ed0c499878f5a6aa3", "d436796fb8f90561c1dc0c97a4c8944e24fd2ae84bd7d38027df551f6ac01393"),
    "audit-1": (0, None, "a8c25c6823eccbec8ca6e579e2d58ebc95e00f4e36066777735b4bbd518eeffc"),
}
assert len(jobs) == 5 and sum(job[0] != 0 for job in jobs.values()) == 1
actual = set()
for path in evidence.glob("*.json"):
    item = json.loads(path.read_text())
    if isinstance(item, dict) and "wrapper" in item and "exit_code" in item:
        if Path(item.get("command", [""])[0]).name in {"lean", "lake"}:
            actual.add(path.stem)
assert actual == set(jobs), actual
for stem, (exit_code, source_hash, log_hash) in jobs.items():
    receipt = load(stem + ".json")
    assert receipt["exit_code"] == exit_code and receipt["log"] == stem + ".log"
    if log_hash:
        assert digest((evidence / receipt["log"]).read_bytes()) == log_hash, stem
    limits, usage = load(stem + ".limits.json"), load(stem + ".usage.json")
    assert limits == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
    assert 0 <= usage["age_seconds"] <= 600 and usage["remaining_percent"] > 1, stem
    assert receipt["wrapper"][1:5] == ["--mem", "4G", "--time", "5m"]
    if source_hash:
        assert receipt["source"] == stem + ".source.lean" and receipt["sha256"] == source_hash
        assert digest((evidence / receipt["source"]).read_bytes()) == source_hash
        assert len(receipt["command"]) == 3 and receipt["command"][1] == "-Dlinter.all=true"
        if "strict" in stem:
            assert not re.search(r"^set_option (?:maxHeartbeats|maxRecDepth)", (evidence / receipt["source"]).read_text(), re.M)
        assert Path(receipt["command"][-1]).name == receipt["source"]
failed = (evidence / "finite-calls-strict-1.log").read_text()
assert len(failed.encode()) == 14081 and len(failed.splitlines()) == 186
assert len(re.findall(r": error:", failed)) == 1
warned = (evidence / "finite-calls-strict-2.log").read_text()
warning_names = ["initial", "frame", "fits", "known", "inputs", "normal", "supported", "causal",
    "merged", "positiveMemo", "origins", "stored", "closed", "nodeIdle", "edgeIdle"]
assert re.findall(r"warning: Variable name `([^`]+)` is not explicitly referenced\.", warned) == warning_names
assert len(re.findall(r"\bwarning(?:\([^)]*\))?:", warned)) == 15
assert not re.search(r"\berror(?:\([^)]*\))?:|\bsorry(?:Ax)?\b", warned)
assert len(warned.encode()) == 6352 and len(warned.splitlines()) == 90
selection = load("selected-sources.json")
assert set(selection) == {"lean/MicroCFTA/" + name + ".lean" for name in selected}
for name, (sha, lines, strict, full) in selected.items():
    path = "lean/MicroCFTA/" + name + ".lean"
    assert selection[path] == dict(sha256=sha, lines=lines, strict=strict, full=full)
    source = (evidence / (name + ".lean")).read_bytes()
    assert digest(source) == sha and len(source.splitlines()) == lines
    assert source == (evidence / (strict + ".source.lean")).read_bytes()
    assert (evidence / (strict + ".log")).read_bytes() == b""
    assert (evidence / (full + ".source.lean")).read_bytes().startswith(source)
    if args.live:
        assert (root / path).read_bytes() == source, path
archive = load("original-source-index.json")["sources"]
assert len(archive) == len(original)
for item in archive:
    name = Path(item["path"]).stem
    assert (item["sha256"], item["lines"]) == original[name]
    data = (evidence / item["snapshot"]).read_bytes()
    assert digest(data) == item["sha256"] and len(data.splitlines()) == item["lines"]
standard = {"Classical.choice", "Quot.sound", "propext"}
assert digest((evidence / "finite-calls-check-full-public.py").read_bytes()) == "6bbdfefff5d8d07499c028fbc2f45d250fa83b6138c0e4cfb6d5cb9f3138f0bf"
for kind, name in [("finite", "SourceCurrentFiniteWarmCalls")]:
    report = load(kind + "-full-readback.json")
    sha, lines, _, full = selected[name]
    raw = (evidence / (full + ".log")).read_bytes()
    printer = (evidence / (full + ".source.lean")).read_text()
    assert report["source_sha256"] == sha and report["source_lines"] == lines
    assert report["printer_sha256"] == digest(printer.encode())
    assert report["log_sha256"] == digest(raw) and report["log_bytes"] == len(raw)
    assert report["all_eight_printer_settings"] and report["no_omissions"] and report["owned_public_job_exit"] == 0
    assert report["exact_module_and_diagnostic_tail"] and report["diagnostic_limits_after_module_only"]
    expected_heads = [("node_calls", "theorem")]
    assert [(head["head"], head["kind"]) for head in report["heads"]] == [("MicroCFTA." + name + "." + head, kind) for head, kind in expected_heads]
    options = ["maxRecDepth 30000", "maxHeartbeats 0", "linter.all true", "pp.explicit true", "pp.fullNames true",
        "pp.proofs true", "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]
    tail = "\n" + "".join("set_option " + option + "\n" for option in options)
    tail += "".join(directive + head["head"] + "\n" for head in report["heads"]
        for directive in ["#check @", "#print ", "#print axioms "])
    assert printer == (evidence / (name + ".lean")).read_text() + tail
    assert len(tail.splitlines()) == 14
    for head in report["heads"]:
        for directive in ["#check @", "#print ", "#print axioms "]:
            assert printer.splitlines().count(directive + head["head"]) == 1
    log = raw.decode()
    assert not re.search(r"sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.", log)
    for head in report["heads"]:
        assert head["check_print_type_identity"] and head["unique_complete_type_body_delimiter"]
        assert set(head["actual_axioms"]) <= standard and head["actual_axioms_within_standard_allowed"]
        assert head.get("private_public_type_names", False) is False and not head.get("private_type_names", [])
        marker = list(re.finditer(r"^(?:@)?" + re.escape(head["head"]) + r" :", log, re.M))
        assert len(marker) == 1
        checked, rest = log[marker[0].end():].split("\n" + head["kind"] + " " + head["head"] + " :", 1)
        normalized = "".join(checked.split())
        matches = [m for m in re.finditer(r" :=\n", rest) if "".join(rest[:m.start()].split()) == normalized]
        assert len(matches) == 1 and len(checked) == head["checked_type_characters"]
        assert not any(token in checked for token in ["_private", "†", "✝", "‡"])
        checked_file = evidence / (kind + "-" + head["head"].split(".")[-1] + "-public-type.txt")
        printed_file = evidence / (kind + "-" + head["head"].split(".")[-1] + "-printed-public-type.txt")
        checked_bytes, printed_bytes = checked_file.read_bytes(), printed_file.read_bytes()
        assert checked_bytes == printed_bytes == checked.encode() == rest[:matches[0].start()].encode()
        assert head["check_print_type_byte_identity"]
        assert len(checked_bytes) == 31520
        assert digest(checked_bytes) == "176e32dc0018cc4bba9f5aad9a2d08ad09a75ef4f589e520d7afe98ebb6ff301"
        helpers = re.findall(r"^private (?:noncomputable )?(?:def|theorem|abbrev) (\w+)", (evidence / (name + ".lean")).read_text(), re.M)
        assert helpers == ["Entry", "advance_entry"] == head["private_namespace_helpers_checked"]
        assert not any("MicroCFTA." + name + "." + helper in normalized for helper in helpers)
        assert rest[matches[0].end():].startswith("fun ")
        axiom = re.search("'" + re.escape(head["head"]) + r"' (depends on axioms:|does not depend on any axioms)", rest)
        assert axiom
        values = re.match(r"\s*\[([^\]]*)\]", rest[axiom.end():]) if axiom.group(1) == "depends on axioms:" else None
        assert values or axiom.group(1) == "does not depend on any axioms"
        axioms = {re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in values.group(1).split(",") if item.strip()} if values else set()
        assert axioms == set(head["actual_axioms"]) and axioms <= standard
audit = (evidence / "audit-1.log").read_text()
build = re.search(r"Build completed successfully \((\d+) jobs\)\.", audit)
dependencies = re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", audit)
assert build and dependencies and not re.search(r"\berror(?:\([^)]*\))?:", audit)
assert int(build.group(1)) == 3622 and int(dependencies.group(1)) == 75262
print(json.dumps(dict(status="PASS", live=args.live, source_jobs=4, audit_jobs=1, actual_jobs=5,
    failed_jobs=1, warned_source_exit_zero_jobs=1, new_lean_lake_jobs=0, selected_modules=1, original_archives=1,
    audit_build_jobs=int(build.group(1)), audit_dependencies=int(dependencies.group(1)),
    audit_log_sha256=digest(audit.encode())), indent=2))
