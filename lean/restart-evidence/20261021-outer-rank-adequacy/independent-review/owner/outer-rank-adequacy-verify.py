"""Verify retained source and check evidence without compiling or evaluating C."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PREFIX = "outer-rank-adequacy-"

def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def relative(name: str) -> Path:
    path = Path(name)
    assert not path.is_absolute() and ".." not in path.parts, name
    return path

def check(path: Path, pin: dict) -> None:
    data = path.read_bytes()
    assert len(data) == pin["bytes"] and digest(data) == pin["sha256"], str(path)

def header(text: str) -> bytes:
    start = text.index("theorem initial_node_call\n")
    return (text[start:text.index("\n := by", start)] + "\n").encode()

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
        first, last = span["start"], span["end"]
        assert 1 <= first <= last <= len(lines)
        excerpt = b"".join(lines[first - 1:last])
        assert len(excerpt) == span["bytes"] and digest(excerpt) == span["sha256"]
        assert (HERE / relative(span["excerpt"])).read_bytes() == excerpt
    if args.live:
        assert pin["authority"] == "root"
        check(args.root / relative(pin["path"]), pin)
source = (HERE / selected["source"]).read_bytes()
assert digest(source) == selected["source_sha256"] and len(source.splitlines()) == selected["source_lines"] == 517 < 650
assert re.findall(r"^(?:noncomputable )?(?:def|theorem) (\w+)", source.decode(), re.M) == ["initial_node_call"]
assert b"set_option maxHeartbeats" not in source and b"set_option maxRecDepth" not in source
assert not re.search(rb"set_option linter\.[^\n]*false|\b(?:sorry|admit)\b", source)
corrected = (HERE / "corrected-public-signature.lean.txt").read_bytes()
original = (HERE / "original-public-signature.lean.txt").read_bytes()
assert header(source.decode()) == corrected and digest(corrected) == selected["exact_header_sha256"]
assert digest(original) == selected["original_header_sha256"]
assert len(original.splitlines()) == len(corrected.splitlines()) == 36
alpha = json.loads((HERE / (PREFIX + "header-alpha-erratum.json")).read_text())
assert len(alpha["warned_names_in_order"]) == alpha["renamed_count"] == 25
inverse = corrected.decode()
for name in alpha["warned_names_in_order"]:
    inverse, count = re.subn(r"\b_" + re.escape(name) + r"\b", name, inverse)
    assert count == 1
assert inverse.encode() == original
before_alpha = (HERE / (PREFIX + "direct-7.source.lean")).read_bytes()
assert source.replace(corrected.rstrip(b"\n"), original.rstrip(b"\n"), 1) == before_alpha
assert digest(before_alpha) == alpha["original_source_sha256"]
assert source.split(b"\n := by", 1)[1] == before_alpha.split(b"\n := by", 1)[1]
ledger = json.loads((HERE / "attempt-ledger.json").read_text())
assert len(ledger["attempts"]) == ledger["actual_lean_jobs"] == selected["actual_lean_jobs"] == 9
assert ledger["nonzero_exit_jobs"] == selected["failed_jobs"] == 6
assert [a["exit_code"] for a in ledger["attempts"]] == [1, 1, 1, 1, 1, 1, 0, 0, 0]
errors = warnings = warned = warned_zero = clean_zero = 0
for attempt in ledger["attempts"]:
    receipt = json.loads((HERE / relative(attempt["receipt"])).read_text())
    assert receipt["exit_code"] == attempt["exit_code"] and attempt["launched_lean"]
    actual_input = (HERE / relative(receipt["source"])).read_bytes()
    assert digest(actual_input) == receipt["sha256"] == attempt["source_sha256"]
    assert receipt["command"][1] == "-Dlinter.all=true" and receipt["wrapper"][1:5] == ["--mem", "4G", "--time", "5m"]
    usage = json.loads((HERE / relative(attempt["usage"])).read_text())
    assert usage["remaining_percent"] > 1 and 0 <= usage["age_seconds"] <= 600
    limits = json.loads((HERE / relative(attempt["limits"])).read_text())
    assert limits == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
    raw = (HERE / relative(attempt["log"])).read_bytes()
    assert digest(raw) == attempt["log_sha256"] and len(raw) == attempt["log_bytes"] and len(raw.splitlines()) == attempt["log_splitlines"]
    err = len(re.findall(rb"(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:", raw))
    warn = len(re.findall(rb"(?m)^.*:\d+:\d+: warning(?:\([^)]*\))?:", raw))
    assert (err, warn) == (attempt["error_diagnostics"], attempt["warning_diagnostics"])
    errors += err
    warnings += warn
    warned += bool(warn)
    warned_zero += bool(warn and receipt["exit_code"] == 0)
    clean_zero += bool(not raw and receipt["exit_code"] == 0) if attempt["kind"] == "strict" else bool(receipt["exit_code"] == 0 and not warn)
assert (errors, warnings, warned, warned_zero, clean_zero) == (40, 28, 2, 1, 2)
repairs = ["direct-1-repair", "direct-2-repair-explicit-fold", "direct-3-repair-stage-bound", "stage-adapter", "direct-5-repair", "direct-6-repair", "header-alpha-erratum"]
for number, repair in enumerate(repairs, 1):
    before = (HERE / (PREFIX + f"direct-{number}.source.lean")).read_text()
    candidate = (HERE / (PREFIX + repair + ".candidate.lean.txt")).read_text()
    assert candidate == (HERE / (PREFIX + f"direct-{number + 1}.source.lean")).read_text()
    saved = (HERE / (PREFIX + repair + ".patch")).read_text()
    labels = saved.splitlines()[:2]
    actual = "".join(difflib.unified_diff(before.splitlines(True), candidate.splitlines(True), fromfile=labels[0][4:], tofile=labels[1][4:]))
    assert actual == saved
strict = json.loads((HERE / (selected["selected_strict"] + ".json")).read_text())
assert strict["exit_code"] == 0 and strict["sha256"] == digest(source) and (HERE / strict["log"]).read_bytes() == b""
printer = (HERE / (PREFIX + "public-1.source.lean")).read_bytes()
assert printer == (HERE / (PREFIX + "full-public.lean")).read_bytes() and printer.startswith(source)
assert len(printer.splitlines()) == 531 and len(printer[len(source):].splitlines()) == 14
readback = json.loads(subprocess.check_output([sys.executable, str(HERE / (PREFIX + "check-full-public.py"))], text=True))
assert readback == json.loads((HERE / (PREFIX + "full-public-readback.json")).read_text())
assert readback["log_bytes"] == selected["public_log_bytes"] == 30964532
assert {h["head"]: h["actual_axioms"] for h in readback["heads"]} == selected["actual_axioms_by_head"]
assert len(readback["heads"]) == selected["new_public_pairs"] == 1
public_type = json.loads((HERE / "public-type-index.json").read_text())
raw = (HERE / public_type["raw_log"]).read_bytes()
assert (HERE / public_type["checked_type_file"]).read_bytes() == raw[public_type["checked_type_start_byte_in_raw"]:public_type["checked_type_end_byte_exclusive_in_raw"]]
assert any(s["path"] == selected["official_path"] and s["sha256"] == digest(source) for s in index["sources"])
command = [sys.executable, str(HERE / "frozen-plan-inputs/verify.py"), "--root", str(args.root)]
if args.live:
    command.append("--live")
assert json.loads(subprocess.check_output(command, text=True))["status"] == "PASS"
assert selected["adequate_outer_root_fuel_proved"] and not selected["capacity_resolved"] and not selected["unconditional_haskell_termination"]
print(json.dumps(dict(status="PASS", live=args.live, local_pins=len(manifest["files"]), root_pins=len(index["sources"]), source_ranges=sum(len(s["reviewed_ranges"]) for s in index["sources"]), actual_lean_jobs=9, nonzero_exit_jobs=6, warned_zero_exit_jobs=1, clean_zero_exit_jobs=2, warning_bearing_jobs=2, new_public_pairs=1, public_log_bytes=30964532, adequate_outer_root_fuel_proved=True, capacity_resolved=False, new_verification_proof_jobs=0), indent=2))
