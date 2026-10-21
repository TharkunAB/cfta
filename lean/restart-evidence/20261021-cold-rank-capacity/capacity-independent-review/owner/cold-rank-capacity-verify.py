"""Verify retained cold proof evidence without compiling or evaluating C."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PREFIX = "cold-rank-capacity-"

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
    start = text.index("theorem constructed_initial_node_call\n")
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
assert digest(source) == selected["source_sha256"]
assert len(source.splitlines()) == selected["source_lines"] == 139 < 250
assert re.findall(rb"^(?:noncomputable )?(?:def|theorem) (\w+)", source, re.M) == [b"constructed_initial_node_call"]
assert not re.search(rb"set_option|\b(?:sorry|admit)\b", source)
original = (HERE / selected["original_header"]).read_bytes()
corrected = (HERE / selected["corrected_header"]).read_bytes()
assert header(source.decode()) == corrected and digest(corrected) == selected["exact_header_sha256"]
assert digest(original) == selected["original_header_sha256"]
assert len(original.splitlines()) == len(corrected.splitlines()) == 25
assert corrected.replace("∃ _built :".encode(), "∃ built :".encode(), 1) == original
warned = (HERE / (PREFIX + "direct-2.source.lean")).read_bytes()
assert source.replace(corrected, original, 1) == warned
assert source.split(b"\n := by", 1)[1] == warned.split(b"\n := by", 1)[1]
repairs = [
    ("original-complete-137.source.lean.txt", "prelaunch-context-placement.source.lean.txt", "prelaunch-context-placement.patch"),
    (PREFIX + "direct-1.source.lean", "direct-1-proposed-repair.source.lean.txt", "direct-1-proposed-repair.patch"),
    (PREFIX + "direct-2.source.lean", "direct-2-proposed-alpha-repair.source.lean.txt", "direct-2-proposed-alpha-repair.patch"),
]
for before_name, after_name, patch_name in repairs:
    before, after = (HERE / before_name).read_text(), (HERE / after_name).read_text()
    saved = (HERE / patch_name).read_text()
    labels = saved.splitlines()[:2]
    assert "".join(difflib.unified_diff(before.splitlines(True), after.splitlines(True), fromfile=labels[0][4:], tofile=labels[1][4:])) == saved
assert (HERE / "prelaunch-context-placement.source.lean.txt").read_bytes() == (HERE / (PREFIX + "direct-1.source.lean")).read_bytes()
assert (HERE / "direct-1-proposed-repair.source.lean.txt").read_bytes() == warned
assert (HERE / "direct-2-proposed-alpha-repair.source.lean.txt").read_bytes() == source
ledger = json.loads((HERE / "attempt-ledger.json").read_text())
assert len(ledger["attempts"]) == ledger["actual_lean_jobs"] == selected["actual_lean_jobs"] == 4
assert [a["exit_code"] for a in ledger["attempts"]] == [1, 0, 0, 0]
errors = warnings = warned_zero = clean_zero = 0
for attempt in ledger["attempts"]:
    receipt = json.loads((HERE / relative(attempt["receipt"])).read_text())
    assert receipt["exit_code"] == attempt["exit_code"] and attempt["launched_lean"]
    actual = (HERE / relative(receipt["source"])).read_bytes()
    assert digest(actual) == receipt["sha256"] == attempt["source_sha256"]
    assert receipt["command"][1] == "-Dlinter.all=true" and receipt["wrapper"][1:5] == ["--mem", "4G", "--time", "5m"]
    usage = json.loads((HERE / relative(attempt["usage"])).read_text())
    assert usage["remaining_percent"] > 1 and 0 <= usage["age_seconds"] <= 600
    assert json.loads((HERE / relative(attempt["limits"])).read_text()) == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
    raw = (HERE / relative(attempt["log"])).read_bytes()
    assert digest(raw) == attempt["log_sha256"] and len(raw) == attempt["log_bytes"] and len(raw.splitlines()) == attempt["log_splitlines"]
    err = len(re.findall(rb"(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:", raw))
    warn = len(re.findall(rb"(?m)^.*:\d+:\d+: warning(?:\([^)]*\))?:", raw))
    assert (err, warn) == (attempt["error_diagnostics"], attempt["warning_diagnostics"])
    errors += err
    warnings += warn
    warned_zero += bool(warn and receipt["exit_code"] == 0)
    clean_zero += bool(receipt["exit_code"] == 0 and not warn and (attempt["kind"] == "FULL" or not raw))
assert (errors, warnings, warned_zero, clean_zero) == (2, 1, 1, 2)
strict = json.loads((HERE / (selected["selected_strict"] + ".json")).read_text())
assert strict["exit_code"] == 0 and strict["sha256"] == digest(source) and (HERE / strict["log"]).read_bytes() == b""
printer = (HERE / (PREFIX + "public-1.source.lean")).read_bytes()
assert printer == (HERE / selected["printer"]).read_bytes() and printer.startswith(source)
assert len(printer.splitlines()) == 153 and len(printer[len(source):].splitlines()) == 14
readback = json.loads(subprocess.check_output([sys.executable, str(HERE / (PREFIX + "check-full-public.py"))], text=True))
assert readback == json.loads((HERE / (PREFIX + "full-public-readback.json")).read_text())
assert readback["log_bytes"] == selected["public_log_bytes"] == 365789
assert {h["head"]: h["actual_axioms"] for h in readback["heads"]} == selected["actual_axioms_by_head"]
assert len(readback["heads"]) == selected["new_public_pairs"] == 1
assert any(p["path"] == selected["official_path"] and p["sha256"] == digest(source) for p in index["sources"])
assert selected["cold_constructed_adequacy_proved"] and not selected["practical_fixed_width_feasibility_proved"]
assert not selected["warm_state_width_transport_proved"] and not selected["unconditional_haskell_termination"]
print(json.dumps(dict(status="PASS", live=args.live, local_pins=len(manifest["files"]), root_pins=len(index["sources"]), source_ranges=sum(len(p["reviewed_ranges"]) for p in index["sources"]), actual_lean_jobs=4, nonzero_exit_jobs=1, warned_zero_exit_jobs=1, clean_zero_exit_jobs=2, new_public_pairs=1, public_log_bytes=365789, new_verification_proof_jobs=0), indent=2))
