"""Verify the retained proof package without compiling or evaluating the recurrence."""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PREFIX = "outer-rank-envelope-"

def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def relative(name: str) -> Path:
    path = Path(name)
    assert not path.is_absolute() and ".." not in path.parts, name
    return path

def check(path: Path, pin: dict) -> None:
    data = path.read_bytes()
    assert len(data) == pin["bytes"] and digest(data) == pin["sha256"], str(path)

def headers(text: str) -> bytes:
    return ("\n".join(text[text.index(start):].split(" :=", 1)[0] + "\n"
        for start in ["noncomputable def envelope", "theorem retains"]) + "\n").encode()

def patch(before: Path, after: Path, before_label: str, after_label: str) -> bytes:
    return "".join(difflib.unified_diff(before.read_text().splitlines(keepends=True),
        after.read_text().splitlines(keepends=True), fromfile=before_label, tofile=after_label)).encode()

parser = argparse.ArgumentParser()
parser.add_argument("--root", type=Path, required=True)
parser.add_argument("--live", action="store_true")
parser.add_argument("--toolchain-source", type=Path)
args = parser.parse_args()
manifest = json.loads((HERE / (PREFIX + "manifest.json")).read_text())
selected = json.loads((HERE / (PREFIX + "selection.json")).read_text())
assert manifest["finalized"] and selected["finalized"]
for item in manifest["files"]:
    check(HERE / relative(item["path"]), item)
pin_data = json.loads((HERE / "source-pins.json").read_text())
assert manifest["sources"] == pin_data["sources"]
toolchain = args.toolchain_source or Path(pin_data["toolchain_source_root"])
for item in manifest["sources"]:
    snapshot = HERE / relative(item["snapshot"])
    check(snapshot, item)
    lines = snapshot.read_bytes().splitlines(keepends=True)
    assert len(lines) == item["lines"]
    for span in item["reviewed_ranges"]:
        first, last = span["start"], span["end"]
        assert 1 <= first <= last <= len(lines)
        block = b"".join(lines[first - 1:last])
        assert digest(block) == span["sha256"]
        expected = "".join(f"{i:5d} {line.decode()}" for i, line in enumerate(lines[first - 1:last], first))
        assert (HERE / relative(span["excerpt"])).read_text() == expected
    if args.live:
        origin = args.root if item["authority"] == "root" else toolchain
        check(origin / relative(item["path"]), item)
source = (HERE / selected["source"]).read_bytes()
text = source.decode()
assert digest(source) == selected["source_sha256"] and len(source.splitlines()) == selected["source_lines"] == 157 < 250
assert re.findall(r"^(?:noncomputable )?(?:def|theorem) (\w+)", text, re.M) == ["envelope", "retains"]
assert headers(text) == (HERE / "frozen-plan-inputs/selected-signatures.lean.txt").read_bytes()
assert digest(headers(text)) == selected["exact_header_sha256"] == "25af429aaa28afb3dab6c396ca47460c4cc72561128611f34d8567ac8bc37e6f"
original = (HERE / "prelaunch-draft-1.source.lean.txt").read_bytes()
assert len(original.splitlines()) == 147
first = (HERE / (PREFIX + "direct-1.source.lean")).read_bytes()
assert original.decode().replace('local notation "Schedule" => SourceCurrentOuterInitialSchedule\n', '').replace("Schedule.", "SourceCurrentOuterInitialSchedule.").encode() == first
assert patch(HERE / "prelaunch-draft-1.source.lean.txt", HERE / (PREFIX + "direct-1.source.lean"),
    "prelaunch-draft-1.source.lean.txt", selected["source"]) == (HERE / "prelaunch-namespace-qualification.patch").read_bytes()
for attempt in [1, 2, 3]:
    before = HERE / (PREFIX + f"direct-{attempt}.source.lean")
    candidate = HERE / f"direct-{attempt}-proposed-repair.source.lean.txt"
    after = HERE / (PREFIX + f"direct-{attempt + 1}.source.lean")
    assert candidate.read_bytes() == after.read_bytes()
    assert patch(before, candidate, before.name, candidate.name) == (HERE / f"direct-{attempt}-proposed-repair.patch").read_bytes()
    assert headers(before.read_text()) == headers(text)
assert (HERE / (PREFIX + "direct-4.source.lean")).read_bytes() == source
ledger = json.loads((HERE / "attempt-ledger.json").read_text())
assert len(ledger["attempts"]) == ledger["actual_lean_jobs"] == 5
assert ledger["failed_jobs"] == 3 and ledger["error_diagnostics"] == 5 and ledger["warning_diagnostics"] == 0
assert [item["exit_code"] for item in ledger["attempts"]] == [1, 1, 1, 0, 0]
assert [item["error_diagnostics"] for item in ledger["attempts"]] == [3, 1, 1, 0, 0]
for attempt in ledger["attempts"]:
    receipt = json.loads((HERE / relative(attempt["receipt"])).read_text())
    assert receipt["exit_code"] == attempt["exit_code"] and attempt["launched_lean"]
    assert digest((HERE / relative(receipt["source"])).read_bytes()) == receipt["sha256"]
    assert receipt["command"][1] == "-Dlinter.all=true"
    assert receipt["wrapper"][1:5] == ["--mem", "4G", "--time", "5m"]
    usage = json.loads((HERE / relative(attempt["usage"])).read_text())
    assert usage["remaining_percent"] == 40 and 0 <= usage["age_seconds"] <= 600
    limits = json.loads((HERE / relative(attempt["limits"])).read_text())
    assert limits == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
    raw = (HERE / relative(attempt["log"])).read_text()
    assert len(re.findall(r"(?m)^.*:\d+:\d+: error(?:\([^)]*\))?:", raw)) == attempt["error_diagnostics"]
    assert len(re.findall(r"(?m)^.*:\d+:\d+: warning(?:\([^)]*\))?:", raw)) == attempt["warning_diagnostics"] == 0
strict = json.loads((HERE / (selected["selected_strict"] + ".json")).read_text())
assert strict["exit_code"] == 0 and strict["sha256"] == selected["source_sha256"]
assert (HERE / strict["log"]).read_bytes() == b""
assert (HERE / (PREFIX + "public-1.input.lean")).read_bytes() == (HERE / (PREFIX + "public-1.source.lean")).read_bytes()
readback = json.loads(subprocess.check_output([sys.executable, str(HERE / (PREFIX + "check-full-public.py"))], text=True))
assert readback == json.loads((HERE / "full-public-readback.json").read_text())
assert len(readback["heads"]) == selected["new_public_pairs"] == 2
assert {item["head"]: item["actual_axioms"] for item in readback["heads"]} == selected["actual_axioms_by_head"]
assert any(item["authority"] == "root" and item["path"] == selected["official_path"] and
    item["sha256"] == selected["source_sha256"] for item in manifest["sources"])
assert selected["envelope_defined"] and selected["entry_retention_proved"]
for key in ["stage_bounds_proved", "adequate_outer_fuel_proved", "physical_adequacy_proved", "capacity_resolved"]:
    assert selected[key] is False
for key in ["infrastructure_attempts", "canonical_jobs", "runtime_jobs", "constructed_pairs", "warning_diagnostics"]:
    assert selected[key] == 0
plan_command = [sys.executable, str(HERE / "frozen-plan-inputs/verify.py"), "--root", str(args.root)]
if args.live:
    plan_command.append("--live")
if args.toolchain_source:
    plan_command += ["--toolchain-source", str(args.toolchain_source)]
plan = json.loads(subprocess.check_output(plan_command, text=True))
assert plan["status"] == "PASS" and not plan["envelope_defined"] and not plan["retention_proved"]
print(json.dumps(dict(status="PASS", live=args.live, local_pins=len(manifest["files"]),
    root_pins=sum(item["authority"] == "root" for item in manifest["sources"]),
    toolchain_pins=sum(item["authority"] == "toolchain" for item in manifest["sources"]),
    source_ranges=sum(len(item["reviewed_ranges"]) for item in manifest["sources"]),
    actual_lean_jobs=5, failed_jobs=3, new_public_pairs=2, public_log_bytes=readback["log_bytes"],
    axioms_by_head=selected["actual_axioms_by_head"], source_only_plan_unchanged=True,
    stage_bounds_proved=False, adequate_outer_fuel_proved=False, new_verification_proof_jobs=0), indent=2))
