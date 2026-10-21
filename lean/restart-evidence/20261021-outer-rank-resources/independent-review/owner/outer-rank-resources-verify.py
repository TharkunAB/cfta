"""Verify the retained proof evidence without compiling or evaluating C."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PREFIX = "outer-rank-resources-"

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
    start = text.index("theorem node_call\n")
    return (text[start:text.index("\n := by", start)] + "\n").encode()

def patch(before: Path, after: Path, one: str, two: str) -> bytes:
    return "".join(difflib.unified_diff(before.read_text().splitlines(True),
        after.read_text().splitlines(True), fromfile=one, tofile=two)).encode()

parser = argparse.ArgumentParser()
parser.add_argument("--root", type=Path, required=True)
parser.add_argument("--toolchain-source", type=Path, required=True)
parser.add_argument("--live", action="store_true")
args = parser.parse_args()
manifest = json.loads((HERE / (PREFIX + "manifest.json")).read_text())
selected = json.loads((HERE / (PREFIX + "selection.json")).read_text())
assert manifest["finalized"] and selected["finalized"]
for pin in manifest["files"]:
    check(HERE / relative(pin["path"]), pin)
pins = json.loads((HERE / "source-pins.json").read_text())
assert manifest["sources"] == pins["sources"]
for pin in pins["sources"]:
    snapshot = HERE / relative(pin["snapshot"])
    check(snapshot, pin)
    lines = snapshot.read_bytes().splitlines(True)
    assert len(lines) == pin["lines"]
    for span in pin["reviewed_ranges"]:
        first, last = span["start"], span["end"]
        assert 1 <= first <= last <= len(lines)
        assert digest(b"".join(lines[first - 1:last])) == span["sha256"]
        excerpt = "".join(f"{n:5d} {line.decode()}" for n, line in enumerate(lines[first - 1:last], first))
        assert (HERE / relative(span["excerpt"])).read_text() == excerpt
    if args.live:
        origin = args.root if pin["authority"] == "root" else args.toolchain_source
        check(origin / relative(pin["path"]), pin)
source = (HERE / selected["source"]).read_bytes()
assert digest(source) == selected["source_sha256"] and len(source.splitlines()) == selected["source_lines"] == 481 < 500
assert re.findall(r"^(?:noncomputable )?(?:def|theorem) (\w+)", source.decode(), re.M) == ["node_call"]
assert header(source.decode()) == (HERE / "frozen-proposed-signature.lean.txt").read_bytes()
assert digest(header(source.decode())) == selected["exact_header_sha256"]
assert b"set_option maxHeartbeats" not in source and b"set_option maxRecDepth" not in source
assert not re.search(rb"SourceCurrentOuterRankEnvelope\.(?:recipe|candidates|images|slot|row|envelope_eq)\b", source)
original = HERE / "first-complete-420.source.lean.txt"
assert len(original.read_bytes().splitlines()) == 420
assert patch(original, HERE / (PREFIX + "direct-1.source.lean"), original.name,
    selected["source"]) == (HERE / "prelaunch-complete-source-cleanup.patch").read_bytes()
for number in range(1, 7):
    before = HERE / (PREFIX + f"direct-{number}.source.lean")
    candidate = HERE / f"direct-{number}-proposed-repair.source.lean.txt"
    after = HERE / (PREFIX + f"direct-{number + 1}.source.lean")
    assert candidate.read_bytes() == after.read_bytes()
    assert patch(before, candidate, before.name, candidate.name) == (HERE / f"direct-{number}-proposed-repair.patch").read_bytes()
    assert header(before.read_text()) == header(source.decode())
assert (HERE / (PREFIX + "direct-7.source.lean")).read_bytes() == source
ledger = json.loads((HERE / "attempt-ledger.json").read_text())
assert len(ledger["attempts"]) == ledger["actual_lean_jobs"] == selected["actual_lean_jobs"] == 8
assert ledger["failed_jobs"] == selected["failed_jobs"] == 6 and ledger["error_diagnostics"] == 43
assert [a["exit_code"] for a in ledger["attempts"]] == [1, 1, 1, 1, 1, 1, 0, 0]
for attempt in ledger["attempts"]:
    receipt = json.loads((HERE / relative(attempt["receipt"])).read_text())
    assert receipt["exit_code"] == attempt["exit_code"] and attempt["launched_lean"]
    assert digest((HERE / relative(receipt["source"])).read_bytes()) == receipt["sha256"]
    assert receipt["command"][1] == "-Dlinter.all=true" and receipt["wrapper"][1:5] == ["--mem", "4G", "--time", "5m"]
    usage = json.loads((HERE / relative(attempt["usage"])).read_text())
    assert usage["remaining_percent"] > 1 and 0 <= usage["age_seconds"] <= 600
    limits = json.loads((HERE / relative(attempt["limits"])).read_text())
    assert limits == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
    raw = (HERE / relative(attempt["log"])).read_bytes()
    assert digest(raw) == attempt["log_sha256"] and len(raw) == attempt["log_bytes"]
    assert len(raw.splitlines()) == attempt["log_splitlines"]
    assert len(re.findall(rb"(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:", raw)) == attempt["error_diagnostics"]
    assert not re.search(rb"(?m)^.*:\d+:\d+: warning(?:\([^)]*\))?:", raw)
strict = json.loads((HERE / (selected["selected_strict"] + ".json")).read_text())
assert strict["exit_code"] == 0 and strict["sha256"] == selected["source_sha256"] and (HERE / strict["log"]).read_bytes() == b""
printer = (HERE / (PREFIX + "public-1.source.lean")).read_bytes()
assert printer == (HERE / (PREFIX + "full-public.lean")).read_bytes() and printer.startswith(source)
assert len(printer.splitlines()) == 495 and len(printer[len(source):].splitlines()) == 14
readback = json.loads(subprocess.check_output([sys.executable, str(HERE / (PREFIX + "check-full-public.py"))], text=True))
assert readback == json.loads((HERE / (PREFIX + "full-public-readback.json")).read_text())
assert readback["log_bytes"] == selected["public_log_bytes"] == 62309163
assert {h["head"]: h["actual_axioms"] for h in readback["heads"]} == selected["actual_axioms_by_head"]
assert len(readback["heads"]) == selected["new_public_pairs"] == 1
outcomes = json.loads((HERE / "metadata-reader-outcomes.json").read_text())
assert outcomes["original_exit_code"] == 143 and outcomes["replacement_exit_code"] == 0
assert outcomes["lean_or_full_jobs_added"] == 0 and not outcomes["actual_full_repeated"]
assert any(s["authority"] == "root" and s["path"] == selected["official_path"] and s["sha256"] == selected["source_sha256"] for s in pins["sources"])
assert selected["conditional_successful_node_resources_proved"] and not selected["adequate_outer_fuel_proved"]
assert not selected["physical_completion_proved"] and not selected["capacity_resolved"]
plan_command = [sys.executable, str(HERE / "frozen-plan-inputs/verify.py"), "--root", str(args.root),
    "--toolchain-source", str(args.toolchain_source)]
if args.live:
    plan_command.append("--live")
assert json.loads(subprocess.check_output(plan_command, text=True))["status"] == "PASS"
print(json.dumps(dict(status="PASS", live=args.live, local_pins=len(manifest["files"]),
    root_pins=sum(s["authority"] == "root" for s in pins["sources"]),
    toolchain_pins=sum(s["authority"] == "toolchain" for s in pins["sources"]),
    source_ranges=sum(len(s["reviewed_ranges"]) for s in pins["sources"]),
    actual_lean_jobs=8, failed_jobs=6, new_public_pairs=1, public_log_bytes=62309163,
    conditional_successful_node_resources_proved=True, adequate_outer_fuel_proved=False,
    new_verification_proof_jobs=0), indent=2))
