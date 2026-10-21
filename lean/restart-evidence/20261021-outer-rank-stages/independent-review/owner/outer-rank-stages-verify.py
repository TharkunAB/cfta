"""Verify the retained proof evidence without compiling or evaluating the envelope."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PREFIX = "outer-rank-stages-"

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
    return ("theorem stage_bounds " + text.split("theorem stage_bounds ", 1)[1].split(" := by\n", 1)[0] + "\n").encode()

def patch(before: Path, after: Path, before_label: str, after_label: str) -> bytes:
    return "".join(difflib.unified_diff(before.read_text().splitlines(keepends=True),
        after.read_text().splitlines(keepends=True), fromfile=before_label, tofile=after_label)).encode()

parser = argparse.ArgumentParser()
parser.add_argument("--root", type=Path, required=True)
parser.add_argument("--toolchain-source", type=Path)
parser.add_argument("--live", action="store_true")
args = parser.parse_args()
manifest = json.loads((HERE / (PREFIX + "manifest.json")).read_text())
selected = json.loads((HERE / (PREFIX + "selection.json")).read_text())
assert manifest["finalized"] and selected["finalized"]
for pin in manifest["files"]:
    check(HERE / relative(pin["path"]), pin)
pins = json.loads((HERE / "source-pins.json").read_text())
assert manifest["sources"] == pins["sources"] and len(pins["sources"]) == 11
toolchain = args.toolchain_source or Path(pins["toolchain_source_root"])
for pin in pins["sources"]:
    snapshot = HERE / relative(pin["snapshot"])
    check(snapshot, pin)
    lines = snapshot.read_bytes().splitlines(keepends=True)
    assert len(lines) == pin["lines"]
    for span in pin["reviewed_ranges"]:
        first, last = span["start"], span["end"]
        assert 1 <= first <= last <= len(lines)
        assert digest(b"".join(lines[first - 1:last])) == span["sha256"]
        excerpt = "".join(f"{n:5d} {line.decode()}" for n, line in enumerate(lines[first - 1:last], first))
        assert (HERE / relative(span["excerpt"])).read_text() == excerpt
    if args.live:
        origin = args.root if pin["authority"] == "root" else toolchain
        check(origin / relative(pin["path"]), pin)
source = (HERE / selected["source"]).read_bytes()
assert digest(source) == selected["source_sha256"] and len(source.splitlines()) == selected["source_lines"] == 242 < 250
assert re.findall(r"^(?:noncomputable )?(?:def|theorem) (\w+)", source.decode(), re.M) == ["stage_bounds"]
assert header(source.decode()) == (HERE / "frozen-plan-inputs/proposed-signature.lean.txt").read_bytes()
assert digest(header(source.decode())) == selected["exact_header_sha256"] == "473b65048b665c273877a1a38f73dce6f2f63001abcd7a40ce79ad86b534293e"
assert b"set_option maxHeartbeats" not in source and b"set_option maxRecDepth" not in source
assert not re.search(rb"SourceCurrentOuterRankEnvelope\.(?:recipe|candidates|images|slot|row|envelope_eq)\b", source)
original = HERE / "original-complete-200.source.lean.txt"
assert len(original.read_bytes().splitlines()) == 200 and original.read_bytes().startswith((HERE / "partial-112.source.lean.txt").read_bytes())
assert patch(original, HERE / (PREFIX + "direct-1.source.lean"), original.name, selected["source"]) == (HERE / "prelaunch-local-proof-annotations.patch").read_bytes()
assert len((HERE / "direct-1-prelaunch-212.source.lean.txt").read_bytes().splitlines()) == 212
for number in range(1, 5):
    before = HERE / (PREFIX + f"direct-{number}.source.lean")
    candidate = HERE / f"direct-{number}-proposed-repair.source.lean.txt"
    after = HERE / (PREFIX + f"direct-{number + 1}.source.lean")
    assert candidate.read_bytes() == after.read_bytes()
    assert patch(before, candidate, before.name, candidate.name) == (HERE / f"direct-{number}-proposed-repair.patch").read_bytes()
    assert header(before.read_text()) == header(source.decode())
assert (HERE / (PREFIX + "direct-5.source.lean")).read_bytes() == source
moved = json.loads((HERE / "direct-3-proposed-repair.json").read_text())["moved_proof_body"]
before_lines = (HERE / (PREFIX + "direct-3.source.lean")).read_bytes().splitlines(keepends=True)
after_lines = (HERE / "direct-3-proposed-repair.source.lean.txt").read_bytes().splitlines(keepends=True)
old_body = b"".join(before_lines[moved["original_first_line"] - 1:moved["original_last_line"]])
new_body = b"".join(after_lines[moved["candidate_first_line"] - 1:moved["candidate_last_line"]])
assert old_body == new_body and digest(old_body) == moved["sha256"]
ledger = json.loads((HERE / "attempt-ledger.json").read_text())
assert len(ledger["attempts"]) == ledger["actual_lean_jobs"] == selected["actual_lean_jobs"] == 6
assert ledger["failed_jobs"] == selected["failed_jobs"] == 4 and ledger["error_diagnostics"] == 18
assert [a["exit_code"] for a in ledger["attempts"]] == [1, 1, 1, 1, 0, 0]
assert [a["error_diagnostics"] for a in ledger["attempts"]] == [10, 3, 2, 3, 0, 0]
for attempt in ledger["attempts"]:
    receipt = json.loads((HERE / relative(attempt["receipt"])).read_text())
    assert receipt["exit_code"] == attempt["exit_code"] and attempt["launched_lean"]
    assert digest((HERE / relative(receipt["source"])).read_bytes()) == receipt["sha256"]
    assert receipt["command"][1] == "-Dlinter.all=true" and receipt["wrapper"][1:5] == ["--mem", "4G", "--time", "5m"]
    usage = json.loads((HERE / relative(attempt["usage"])).read_text())
    assert usage["remaining_percent"] == 39 and 0 <= usage["age_seconds"] <= 600
    limits = json.loads((HERE / relative(attempt["limits"])).read_text())
    assert limits == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
    raw = (HERE / relative(attempt["log"])).read_bytes()
    assert digest(raw) == attempt["log_sha256"] and len(raw) == attempt["log_bytes"]
    assert len(re.findall(rb"(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:", raw)) == attempt["error_diagnostics"]
    assert not re.search(rb"(?m)^.*:\d+:\d+: warning(?:\([^)]*\))?:", raw)
strict = json.loads((HERE / (selected["selected_strict"] + ".json")).read_text())
assert strict["exit_code"] == 0 and strict["sha256"] == selected["source_sha256"] and (HERE / strict["log"]).read_bytes() == b""
printer = (HERE / (PREFIX + "public-1.source.lean")).read_bytes()
assert printer == (HERE / (PREFIX + "full-input.lean")).read_bytes() and printer.startswith(source)
assert len(printer.splitlines()) == 256 and len(printer[len(source):].splitlines()) == 14
readback = json.loads(subprocess.check_output([sys.executable, str(HERE / (PREFIX + "check-full-public.py"))], text=True))
assert readback == json.loads((HERE / (PREFIX + "full-public-readback.json")).read_text())
assert len(readback["heads"]) == selected["new_public_pairs"] == 1 and readback["log_bytes"] == 381822
assert {h["head"]: h["actual_axioms"] for h in readback["heads"]} == selected["actual_axioms_by_head"]
assert digest((HERE / (PREFIX + "public-type.txt")).read_bytes()) == "0e9bbf46bf835cadbc5039204859405522b83c1776711b74244341086f68b6cb"
assert (HERE / (PREFIX + "public-type.txt")).read_bytes() == (HERE / (PREFIX + "printed-type.txt")).read_bytes()
assert any(s["authority"] == "root" and s["path"] == selected["official_path"] and s["sha256"] == selected["source_sha256"] for s in pins["sources"])
assert selected["stage_bounds_proved"] and selected["proof_factoring_default_per_declaration_limits_unchanged"]
for key in ["physical_stage_correspondence_proved", "same_global_root_resources_proved", "actual_intermediate_peaks_proved", "actual_nested_lower_fuels_proved", "adequate_outer_fuel_proved", "physical_adequacy_proved", "capacity_resolved"]:
    assert selected[key] is False
for key in ["infrastructure_attempts", "canonical_jobs", "runtime_jobs", "constructed_pairs", "warning_diagnostics"]:
    assert selected[key] == 0
cue = json.loads((HERE / "root-verification-cue.json").read_text())
assert cue["root_reported_strict_exit"] == cue["root_reported_audit_exit"] == 0
assert cue["root_reported_audit_jobs"] == 3615 and cue["root_reported_audit_dependencies"] == 75149
assert cue["reported_global_actual_jobs"] == 8 and cue["reported_global_failed_jobs"] == 4
plan_command = [sys.executable, str(HERE / "frozen-plan-inputs/verify.py"), "--root", str(args.root), "--toolchain-source", str(toolchain)]
if args.live:
    plan_command.append("--live")
plan = json.loads(subprocess.check_output(plan_command, text=True))
assert plan["status"] == "PASS" and not plan["stage_bounds_proved"] and not plan["implementation_authorized"]
print(json.dumps(dict(status="PASS", live=args.live, local_pins=len(manifest["files"]), root_pins=6,
    toolchain_pins=5, source_ranges=23, actual_lean_jobs=6, failed_jobs=4, new_public_pairs=1,
    public_log_bytes=381822, axioms_by_head=selected["actual_axioms_by_head"], source_only_plan_unchanged=True,
    stage_bounds_proved=True, adequate_outer_fuel_proved=False, new_verification_proof_jobs=0), indent=2))
