"""Check saved cold finite warm-call proof evidence. This script does not run Lean."""
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
evidence = root / "lean/restart-evidence/20261021-cold-finite-warm-calls"
def load(name):
    return json.loads((evidence / name).read_text())
def digest(data):
    return hashlib.sha256(data).hexdigest()

selected = {
    "SourceCurrentColdFiniteWarmCalls": ("e4665b0bb522ec88f1925fe6bc360b76e9e4bdfbe6192210ac708a3097a20cc5", 157, "cold-finite-calls-strict-2", "cold-finite-calls-public-2"),
}
original = {
    "Audit": ("d11e901227fa107e2b36ebd5a76f96f1f89f7f8f697e39be2907011648cf9487", 3111),
}
jobs = {
    "cold-finite-calls-strict-1": (0, "3299d48ee9c5ba1d09cbc25c88946b0b67ecc86ac028df67b30eadae8ae40a9d", hashlib.sha256(b"").hexdigest()),
    "cold-finite-calls-public-1": (0, "c15b5496804e405b5cd740f862540ec4754388762ddbd0b1c4d1afc33f99ec33", "ce8d6f9021c746e8c0b824544f458a0ae51259efbe4ac129e665bfe42d84f8aa"),
    "cold-finite-calls-strict-2": (0, selected["SourceCurrentColdFiniteWarmCalls"][0], hashlib.sha256(b"").hexdigest()),
    "cold-finite-calls-public-2": (0, "a0a6d1dd326c17cb4c46bae03a5e1f797df6e8030554d8576a03fd64eb39f160", "d84c0cdcd3e399a5f75fea97834a3d651ac25003dce70615e5cc3781edcbce9d"),
    "cold-finite-calls-audit-1": (0, None, "a64c52004a4efc52f348fd0328a1c77eda1fffbb7a01424d2b7a196d9e5b1346"),
}
assert len(jobs) == 5 and sum(job[0] != 0 for job in jobs.values()) == 0
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
            assert (evidence / (stem + ".log")).read_bytes() == b""
            assert not re.search(r"^set_option (?:maxHeartbeats|maxRecDepth)", (evidence / receipt["source"]).read_text(), re.M)
        assert Path(receipt["command"][-1]).name == receipt["source"]
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
assert digest((evidence / "cold-finite-calls-check-full-public.py").read_bytes()) == "4daead2c07b238508524d2f366eba273f1ca8a673146090ebcf288075d13b8d4"
for kind, name in [("cold-finite", "SourceCurrentColdFiniteWarmCalls")]:
    report = load(kind + "-full-readback.json")
    sha, lines, _, full = selected[name]
    raw = (evidence / (full + ".log")).read_bytes()
    printer = (evidence / (full + ".source.lean")).read_text()
    assert report["source_sha256"] == sha and report["source_lines"] == lines
    assert report["printer_sha256"] == digest(printer.encode())
    assert report["log_sha256"] == digest(raw) and report["log_bytes"] == len(raw)
    assert report["all_eight_printer_settings"] and report["no_omissions"] and report["owned_public_job_exit"] == 0
    assert report["exact_module_and_diagnostic_tail"] and report["diagnostic_limits_after_module_only"]
    expected_heads = [("constructed_node_calls", "theorem")]
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
        assert len(checked_bytes) == 21121 and len(checked) == 21099
        assert digest(checked_bytes) == "82edd836ff1da14c590e9fc9a4b8223955258f138a821be6dea8253920a11b8d"
        helpers = re.findall(r"^private (?:noncomputable )?(?:def|theorem|abbrev) (\w+)", (evidence / (name + ".lean")).read_text(), re.M)
        assert helpers == [] == head["private_namespace_helpers_checked"]
        assert checked.count("MicroCFTA.FormulaExecutable.formulaDecidableEq") == 2
        assert len(checked_bytes.splitlines()) == 268 and checked_bytes.count(b"\n") == 267 and not checked_bytes.endswith(b"\n")
        assert not any("MicroCFTA." + name + "." + helper in normalized for helper in helpers)
        assert rest[matches[0].end():].startswith("fun ")
        axiom = re.search("'" + re.escape(head["head"]) + r"' (depends on axioms:|does not depend on any axioms)", rest)
        assert axiom
        values = re.match(r"\s*\[([^\]]*)\]", rest[axiom.end():]) if axiom.group(1) == "depends on axioms:" else None
        assert values or axiom.group(1) == "does not depend on any axioms"
        axioms = {re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in values.group(1).split(",") if item.strip()} if values else set()
        assert axioms == set(head["actual_axioms"]) and axioms <= standard
        assert len(rest[matches[0].end():axiom.start()]) == head["body_characters"] == 688912
rejected = load("rejected-v1-public-type-review.json")
assert rejected["status"] == "REJECTED_PUBLIC_TYPE_HYGIENE" and rejected["actual_FULL_exit_code"] == 0 and rejected["metadata_reader_exit_code"] == 1
badraw = (evidence / "cold-finite-calls-public-1.log").read_bytes()
assert len(badraw) == 733971 and digest(badraw) == rejected["raw_sha256"]
badlog = badraw.decode(); badname = "MicroCFTA.SourceCurrentColdFiniteWarmCalls.constructed_node_calls"
badmarkers = list(re.finditer(r"^(?:@)?" + re.escape(badname) + r" :", badlog, re.M)); assert len(badmarkers) == 1
badchecked, badrest = badlog[badmarkers[0].end():].split("\ntheorem " + badname + " :", 1)
badmatches = [m for m in re.finditer(r" :=\n", badrest) if "".join(badrest[:m.start()].split()) == "".join(badchecked.split())]
assert len(badmatches) == 1 and badrest[badmatches[0].end():].startswith("fun ")
assert not re.search(r"sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.", badlog)
bad_axiom = re.search("'" + re.escape(badname) + r"' (depends on axioms:|does not depend on any axioms)", badrest); assert bad_axiom
bad_values = re.match(r"\s*\[([^\]]*)\]", badrest[bad_axiom.end():]) if bad_axiom.group(1) == "depends on axioms:" else None
assert bad_values or bad_axiom.group(1) == "does not depend on any axioms"
assert ({re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in bad_values.group(1).split(",") if item.strip()} if bad_values else set()) <= standard
badtype = (evidence / "rejected-v1-constructed_node_calls-public-type.txt").read_bytes()
assert badtype == (evidence / "rejected-v1-constructed_node_calls-printed-public-type.txt").read_bytes() == badchecked.encode() == badrest[:badmatches[0].start()].encode()
assert len(badtype) == 21163 and digest(badtype) == rejected["TYPE_sha256"] == "95b4ce3079effe4abb1494d24adc23016d05fde243a63f21c564293706dad373"
assert len(badtype.splitlines()) == 268 and badtype.count(b"\n") == 267 and not badtype.endswith(b"\n")
assert badchecked.count("MicroCFTA.SourceCurrentOuterCopiedWarmHit.instDecidableEqFormula✝") == 2 and badchecked.count("MicroCFTA.FormulaExecutable.formulaDecidableEq") == 0
assert badchecked.count("✝") == 2 and not any(marker in badchecked for marker in ["_private", "†", "‡"])
badsource = (evidence / "cold-finite-calls-strict-1.source.lean").read_bytes()
assert len(badsource.splitlines()) == 153 and (evidence / "cold-finite-calls-public-1.source.lean").read_text() == badsource.decode() + tail
badarchive = evidence / "explicit-instance-repair/actual-rejected-FULL1"
assert (evidence / "full-reader-1.stdout").read_bytes() == (badarchive / "full-reader-1.stdout").read_bytes() == b""
assert (evidence / "full-reader-1.stderr").read_bytes() == (badarchive / "full-reader-1.stderr").read_bytes() != b""
assert (badarchive / "cold-finite-calls-public-1.log").read_bytes() == badraw
assert (badarchive / "rejected-checked-TYPE.txt").read_bytes() == badtype
reader_archive = evidence / "proof-verifier-preparation-v2/reader1-root-evidence"
reader_stem = "mcfta-cold-finite-warm-calls-full-reader-1."
reader_pins = {'json': 'ddf2324251f8c719ebe2a1c43c79d9784c2090c1843dcf416b722a4dd0b42857', 'log': '82fde320716b9ac8942319df338ea96d237f6974acedccd2820f04eed7b6997e', 'limits.json': '408bad6c1715f2c15adecf485dbfcb2753512b2f94e0a96011ddef6f6650faf3', 'peaks.txt': 'd3256fa8e8fb8bb1ece79e1fce7feb600b8eb5cce85fc24b7cacbb043a655cfc', 'source.py': 'cc80826b1704d5e624f77a2e82fe3627258df4b427dd38b6b08db940ae4847cd', 'usage.json': '8e63f5a9a637401031c7713fa83c269f6fd1a85e3c253dd480dddf056f76caad'}
for suffix, sha in reader_pins.items():
    assert digest((reader_archive / (reader_stem + suffix)).read_bytes()) == sha
reader_receipt = json.loads((reader_archive / (reader_stem + "json")).read_text())
assert reader_receipt["exit_code"] == 1 and Path(reader_receipt["command"][0]).name == "python3"
assert reader_receipt["wrapper"][1:5] == ["--mem", "4G", "--time", "5m"]
assert json.loads((reader_archive / (reader_stem + "limits.json")).read_text()) == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
reader_usage = json.loads((reader_archive / (reader_stem + "usage.json")).read_text())
assert 0 <= reader_usage["age_seconds"] <= 600 and reader_usage["remaining_percent"] > 1
assert (root / "lean/MicroCFTA/Audit.lean").read_bytes().replace(b"import MicroCFTA.SourceCurrentColdFiniteWarmCalls\n", b"", 1) == (evidence / "original-sources/Audit.original.lean.txt").read_bytes()
audit = (evidence / "cold-finite-calls-audit-1.log").read_text()
build = re.search(r"Build completed successfully \((\d+) jobs\)\.", audit)
dependencies = re.search(r"Checked axiom dependencies of (\d+) MicroCFTA theorems", audit)
assert build and dependencies and not re.search(r"\berror(?:\([^)]*\))?:", audit)
assert int(build.group(1)) == 3623 and int(dependencies.group(1)) == 75263
print(json.dumps(dict(status="PASS", live=args.live, source_jobs=4, audit_jobs=1, actual_jobs=5,
    failed_jobs=0, warned_source_exit_zero_jobs=0, rejected_public_type_jobs=1, new_lean_lake_jobs=0, selected_modules=1, original_archives=1,
    audit_build_jobs=int(build.group(1)), audit_dependencies=int(dependencies.group(1)),
    audit_log_sha256=digest(audit.encode())), indent=2))
