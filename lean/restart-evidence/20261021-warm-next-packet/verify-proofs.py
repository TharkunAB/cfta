"""Check saved warm next-packet proof evidence. This script does not run Lean."""
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
evidence = root / "lean/restart-evidence/20261021-warm-next-packet"
def load(name):
    return json.loads((evidence / name).read_text())
def digest(data):
    return hashlib.sha256(data).hexdigest()

selected = {
    "SourceCurrentWarmNextPacket": ("13e8373cff925aca8832a47e12514767dd94dbe3fdb8d68bd73b2cdf19246be8", 117, "warm-packet-strict-1", "warm-packet-public-1"),
}
original = {
    "Audit": ("dde44b93bbc658d4aa7decec70afff57c6680b0878df6af7c510325006067a0a", 3109),
}
jobs = {
    "warm-packet-strict-1": (0, selected["SourceCurrentWarmNextPacket"][0], hashlib.sha256(b"").hexdigest()),
    "warm-packet-public-1": (0, "2fa0e8e568ecc8a2decd9575448cc1ab264c888c018131ec1bd8ef33b293279d", "68cd5d5bf82cfb8fa7d0d1877c5ec78bcd9fff18052735354ba6a61ec6cbfc48"),
    "audit-1": (0, None, "c12aad3737ece46dbf7edbf18700e5c971f0d710d21183891c37c74ab86f01e9"),
}
assert len(jobs) == 3 and sum(job[0] != 0 for job in jobs.values()) == 0
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
assert digest((evidence / "warm-packet-check-full-public.py").read_bytes()) == "95229fc1023967865d5ff2db32e3303e59d8abc43223228573755010bc3ecc5f"
for kind, name in [("warm", "SourceCurrentWarmNextPacket")]:
    report = load(kind + "-full-readback.json")
    sha, lines, _, full = selected[name]
    raw = (evidence / (full + ".log")).read_bytes()
    printer = (evidence / (full + ".source.lean")).read_text()
    assert report["source_sha256"] == sha and report["source_lines"] == lines
    assert report["printer_sha256"] == digest(printer.encode())
    assert report["log_sha256"] == digest(raw) and report["log_bytes"] == len(raw)
    assert report["all_eight_printer_settings"] and report["no_omissions"] and report["owned_public_job_exit"] == 0
    expected_heads = [("node_call", "theorem")]
    assert [(head["head"], head["kind"]) for head in report["heads"]] == [("MicroCFTA." + name + "." + head, kind) for head, kind in expected_heads]
    options = ["maxRecDepth 30000", "maxHeartbeats 0", "linter.all true", "pp.explicit true", "pp.fullNames true",
        "pp.proofs true", "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"]
    tail = "\n" + "".join("set_option " + option + "\n" for option in options)
    tail += "".join(directive + head["head"] + "\n" for head in report["heads"]
        for directive in ["#check @", "#print ", "#print axioms "])
    assert printer == (evidence / (name + ".lean")).read_text() + tail
    log = raw.decode()
    assert not re.search(r"sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|⋯|…|\.\.\.", log)
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
        assert "".join((evidence / (kind + "-" + head["head"].split(".")[-1] + "-public-type.txt")).read_text().split()) == normalized
        helpers = re.findall(r"^private (?:noncomputable )?(?:def|theorem|abbrev) (\w+)", (evidence / (name + ".lean")).read_text(), re.M)
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
print(json.dumps(dict(status="PASS", live=args.live, source_jobs=2, audit_jobs=1, actual_jobs=3,
    failed_jobs=0, new_lean_lake_jobs=0, selected_modules=1, original_archives=1,
    audit_build_jobs=int(build.group(1)), audit_dependencies=int(dependencies.group(1)),
    audit_log_sha256=digest(audit.encode())), indent=2))
