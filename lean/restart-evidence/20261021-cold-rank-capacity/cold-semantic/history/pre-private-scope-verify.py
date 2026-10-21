"""Verify retained semantic proof evidence without compiling or evaluating C."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PREFIX = "cold-rank-semantic-"
digest = lambda data: hashlib.sha256(data).hexdigest()

def relative(name: str) -> Path:
    path = Path(name)
    assert not path.is_absolute() and ".." not in path.parts, name
    return path

def check(path: Path, pin: dict) -> None:
    data = path.read_bytes()
    assert len(data) == pin["bytes"] and digest(data) == pin["sha256"], str(path)

def header(text: str) -> bytes:
    first = text.index("theorem constructed_initial_node_call\n")
    return (text[first:text.index("\n := by", first)] + "\n").encode()

parser = argparse.ArgumentParser()
parser.add_argument("--root", type=Path, required=True)
parser.add_argument("--live", action="store_true")
args = parser.parse_args()
manifest = json.loads((HERE / (PREFIX + "manifest.json")).read_text())
selected = json.loads((HERE / (PREFIX + "selection.json")).read_text())
assert manifest["finalized"] and selected["finalized"]
for pin in manifest["files"]:
    check(HERE / relative(pin["path"]), pin)
index = json.loads((HERE / "source-index.json").read_text())
assert manifest["sources"] == index["sources"]
for pin in index["sources"]:
    snapshot = HERE / relative(pin["snapshot"])
    check(snapshot, pin)
    lines = snapshot.read_bytes().splitlines(True)
    assert len(lines) == pin["lines"]
    for span in pin["reviewed_ranges"]:
        assert 1 <= span["start"] <= span["end"] <= len(lines)
        part = b"".join(lines[span["start"] - 1:span["end"]])
        assert len(part) == span["bytes"] and digest(part) == span["sha256"]
        assert part == (HERE / relative(span["excerpt"])).read_bytes()
    if args.live:
        assert pin["authority"] == "root"
        check(args.root / relative(pin["path"]), pin)
source = (HERE / selected["source"]).read_bytes()
assert digest(source) == selected["source_sha256"] and len(source.splitlines()) == selected["source_lines"] == 120 < 250
assert re.findall(r"^(?:noncomputable )?(?:def|theorem) (\w+)", source.decode(), re.M) == ["constructed_initial_node_call"]
assert b"set_option maxHeartbeats" not in source and b"set_option maxRecDepth" not in source
assert not re.search(rb"set_option linter\.[^\n]*false|\b(?:sorry|admit)\b", source)
corrected = (HERE / "corrected-proposed-signature.lean.txt").read_bytes()
original = (HERE / "proposed-signature.lean.txt").read_bytes()
assert header(source.decode()) == corrected and digest(corrected) == selected["exact_header_sha256"]
assert len(corrected.splitlines()) == len(original.splitlines()) == 30
assert corrected.replace("∃ _built :".encode(), "∃ built :".encode(), 1) == original
before = (HERE / "history/pre-header-alpha-120.source.lean.txt").read_bytes()
assert source.replace(corrected.rstrip(b"\n"), original.rstrip(b"\n"), 1) == before
assert source.split(b"\n := by", 1)[1] == before.split(b"\n := by", 1)[1]
patch = "".join(difflib.unified_diff(before.decode().splitlines(True), source.decode().splitlines(True), fromfile=selected["source"], tofile=PREFIX + "header-alpha-erratum.candidate.lean.txt"))
assert patch == (HERE / (PREFIX + "header-alpha-erratum.patch")).read_text()
assert source.count(b"SourceCurrentColdRankCapacity.constructed_initial_node_call") == 1
assert source.count(b"SourceCurrentConstructedOuterInitial.node_call") == 1
ledger = json.loads((HERE / "attempt-ledger.json").read_text())
assert len(ledger["attempts"]) == ledger["actual_lean_jobs"] == selected["actual_lean_jobs"] == 2
assert ledger["nonzero_exit_jobs"] == ledger["warning_bearing_jobs"] == 0
for attempt in ledger["attempts"]:
    receipt = json.loads((HERE / relative(attempt["receipt"])).read_text())
    assert receipt["exit_code"] == attempt["exit_code"] == 0 and attempt["launched_lean"]
    assert digest((HERE / relative(receipt["source"])).read_bytes()) == receipt["sha256"] == attempt["source_sha256"]
    assert receipt["command"][1] == "-Dlinter.all=true" and receipt["wrapper"][1:5] == ["--mem", "4G", "--time", "5m"]
    usage = json.loads((HERE / relative(attempt["usage"])).read_text())
    assert usage["remaining_percent"] > 1 and 0 <= usage["age_seconds"] <= 600
    limits = json.loads((HERE / relative(attempt["limits"])).read_text())
    assert limits == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
    raw = (HERE / relative(attempt["log"])).read_bytes()
    assert len(raw) == attempt["log_bytes"] and digest(raw) == attempt["log_sha256"] and len(raw.splitlines()) == attempt["log_splitlines"]
    assert not re.search(rb"(?m)^.*:\d+:\d+: (?:error|warning)(?:\([^)]*\))?:", raw)
strict = json.loads((HERE / (selected["selected_strict"] + ".json")).read_text())
assert strict["sha256"] == digest(source) and (HERE / strict["log"]).read_bytes() == b""
printer = (HERE / (PREFIX + "public-1.source.lean")).read_bytes()
assert printer == (HERE / (PREFIX + "full-printer.lean")).read_bytes() and printer.startswith(source)
assert len(printer.splitlines()) == 134 and len(printer[len(source):].splitlines()) == 14
readback = json.loads(subprocess.check_output([sys.executable, str(HERE / (PREFIX + "check-full-public.py"))], text=True))
assert readback == json.loads((HERE / (PREFIX + "full-public-readback.json")).read_text())
assert readback["log_bytes"] == selected["public_log_bytes"] == 1330639
assert {head["head"]: head["actual_axioms"] for head in readback["heads"]} == selected["actual_axioms_by_head"]
assert len(readback["heads"]) == selected["new_public_pairs"] == 1
public_type = json.loads((HERE / "public-type-index.json").read_text())
raw = (HERE / public_type["raw_log"]).read_bytes()
assert (HERE / public_type["checked_type_file"]).read_bytes() == raw[public_type["start_byte"]:public_type["end_byte_exclusive"]]
assert any(pin["path"] == selected["official_path"] and pin["sha256"] == digest(source) for pin in index["sources"])
command = [sys.executable, str(HERE / "frozen-plan-inputs/verify.py"), "--root", str(args.root)]
if args.live:
    command.append("--live")
assert json.loads(subprocess.check_output(command, text=True))["status"] == "PASS"
assert selected["modeled_cold_stored_language_equivalence_proved"] and not selected["solver_completeness_proved"] and not selected["exported_table_exactness_proved"]
print(json.dumps(dict(status="PASS", live=args.live, local_pins=len(manifest["files"]), root_pins=len(index["sources"]), source_ranges=sum(len(pin["reviewed_ranges"]) for pin in index["sources"]), actual_lean_jobs=2, nonzero_exit_jobs=0, warning_bearing_jobs=0, new_public_pairs=1, public_log_bytes=1330639, modeled_cold_stored_language_equivalence_proved=True, new_verification_proof_jobs=0), indent=2))
