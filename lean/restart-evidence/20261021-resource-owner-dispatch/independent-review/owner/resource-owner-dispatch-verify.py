#!/usr/bin/env python3
"""Verify the frozen immediate dispatch proof without running Lean."""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
PREFIX = "resource-owner-dispatch-"
HEAD = "MicroCFTA.SourceCurrentResourceOwnerDispatch.key_ne_top"

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path: Path) -> dict:
    return json.loads(path.read_text())

def relative(value: str) -> Path:
    path = Path(value)
    assert not path.is_absolute() and ".." not in path.parts, value
    return path

def check(path: Path, pin: dict) -> None:
    assert path.is_file() and path.stat().st_size == pin["bytes"] and sha(path) == pin["sha256"], str(path)

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    manifest = read(HERE / (PREFIX + "manifest.json"))
    assert manifest["finalized"]
    for pin in manifest["files"]:
        check(HERE / relative(pin["path"]), pin)
    pins = read(HERE / (PREFIX + "source-pins.json"))["sources"]
    assert pins == manifest["sources"] and len(pins) == 14
    for pin in pins:
        snapshot = HERE / relative(pin["snapshot"])
        check(snapshot, pin)
        lines = snapshot.read_bytes().splitlines(keepends=True)
        for span in pin["reviewed_ranges"]:
            lo, hi = span["start"], span["end"]
            assert 1 <= lo <= hi <= len(lines)
            assert hashlib.sha256(b"".join(lines[lo-1:hi])).hexdigest() == span["sha256"]
        if args.live:
            check(args.root / relative(pin["path"]), pin)
    selected = read(HERE / (PREFIX + "selection.json"))
    assert selected["finalized"] and selected["public_heads"] == [HEAD]
    assert selected["lean_jobs"] == 3 and selected["failed_checks"] == 1
    assert selected["warning_checks"] == selected["infrastructure_attempts"] == selected["canonical_jobs"] == selected["constructed_pairs"] == 0
    assert selected["new_public_pairs"] == 1 and selected["official_edits_by_author"] is False
    source = HERE / selected["source"]
    assert sha(source) == selected["source_sha256"] == "1e287d68471babbaf486eee9e224ce5ed5cd3e9f30544053fd82da0e4c71ad7b"
    text = source.read_text()
    assert len(text.splitlines()) == selected["source_lines"] == 187
    assert re.findall(r"^theorem (\w+)", text, re.M) == ["key_ne_top"]
    assert re.findall(r"^private theorem (\w+)", text, re.M) == ["reservation"]
    assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private", text)
    proposal = (HERE / "inputs/plan/proposed-signature.lean.txt").read_text()
    assert text.split("theorem key_ne_top\n", 1)[1].split(" := by", 1)[0] == proposal.split("theorem key_ne_top\n", 1)[1].split("\nend MicroCFTA.", 1)[0]
    assert selected["public_header_byte_exact_frozen_proposal"]
    assert text.count("SourceCurrentResourceParentWriters.edge_call formulas solver") == 1
    assert text.count("SourceCurrentResourceOwnerProgress.key_ne_top formulas solver") == 1
    assert text.count("SourceCurrentOuterPrefixNativeStores.reached formulas solver") == 3
    assert "SourceCurrentOuterOwnerSelection.selected" not in text
    before = (HERE / (PREFIX + "direct-1.source.lean")).read_text()
    assert text == before.replace("(.node ownerEntry ownerRows ownerDepth ownerFree).referenceOf :=", "(.node ownerEntry ownerRows ownerDepth ownerFree : Node).referenceOf :=")
    prelaunch = (HERE / "dispatch-prelaunch-1.source.lean").read_text()
    assert sha(HERE / "dispatch-prelaunch-1.source.lean") == "034af6c7ba37f80344385bd222afae5595a7a43b03aec69da1f0738d4a500dec"
    assert before == prelaunch.replace("  simp only [SourceCurrentOuterInitialPrefix.forecast,SourceCurrentOuterInitialSchedule.rows] at headRoom", "  change Room bits (SourceCurrentOuterInitialSchedule.rows ((fuel + slot + 1) + 1) budget rowSeed).2 at headRoom\n  rw [SourceCurrentOuterInitialSchedule.rows] at headRoom")
    attempts = read(HERE / (PREFIX + "attempt-ledger.json"))["attempts"]
    expected = {PREFIX + "direct-1": 1, PREFIX + "direct-2": 0, PREFIX + "public-1": 0}
    assert len(attempts) == 3 and {item["name"]: item["exit_code"] for item in attempts} == expected
    assert {path.stem for path in HERE.glob(PREFIX + "*.json") if re.fullmatch(PREFIX + r"(?:direct|public)-\d+", path.stem)} == set(expected)
    for item in attempts:
        stem = item["name"]
        receipt = read(HERE / (stem + ".json"))
        assert item["lean_launched"] and receipt["exit_code"] == item["exit_code"]
        assert sha(HERE / (stem + ".json")) == item["receipt_sha256"]
        assert sha(HERE / (stem + ".log")) == item["log_sha256"]
        assert sha(HERE / receipt["source"]) == receipt["sha256"] == item["source_sha256"]
        assert read(HERE / (stem + ".limits.json")) == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
        usage = read(HERE / (stem + ".usage.json"))
        assert 0 <= usage["age_seconds"] < 120 and usage["remaining_percent"] > 1
        assert usage["remaining_percent"] == item["usage_remaining_percent"]
        assert receipt["wrapper"][1:5] == ["--mem", "4G", "--time", "5m"]
        assert receipt["command"][0].endswith("lean4---v4.34.1/bin/lean") and receipt["command"][1] == "-Dlinter.all=true"
        assert not re.search(r"\bwarning(?:\([^)]*\))?:", (HERE / (stem + ".log")).read_text())
    strict, public = selected["selected_strict"], selected["selected_public"]
    assert not (HERE / (strict + ".log")).read_bytes()
    assert (HERE / (strict + ".source.lean")).read_bytes() == source.read_bytes()
    assert (HERE / (PREFIX + "direct-1.log")).read_text().count("error(lean.invalidDottedIdent):") == 1
    full = HERE / (public + ".log")
    assert full.stat().st_size == selected["public_log_bytes"] == 9274578
    assert sha(full) == selected["public_log_sha256"] == "3290e0161977d35675aa03a2796b3a4bf8257ef3979eadceb7fc03eb3de6daec"
    log = full.read_text()
    assert not re.search(r"sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.", log)
    checked, printed = log.split("@" + HEAD + " :", 1)[1].split("\ntheorem " + HEAD + " :", 1)
    delimiters = list(re.finditer(r" :=\n(?=fun\b)", printed))
    assert len(delimiters) == 1
    boundary = delimiters[0]
    declared, proof = printed[:boundary.start()], printed[boundary.end():]
    assert "".join(checked.split()) == "".join(declared.split()) and "_private" not in checked + declared
    printer = (HERE / (public + ".source.lean")).read_text()
    assert printer.startswith(text + "\n")
    for option in ("linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"):
        assert printer.count("set_option " + option) == 1
    for directive in ("#check @", "#print ", "#print axioms "):
        assert printer.count(directive + HEAD + "\n") == 1
    match = re.search(re.escape("'" + HEAD + "' depends on axioms:") + r"\s*\[([^\]]*)\]", proof)
    assert match and len(proof[:match.start()]) > 1000
    names = sorted(item.strip() for item in re.sub(r"\.\{[^}]*\}", "", match.group(1)).split(","))
    assert names == selected["axioms_by_head"][HEAD] == ["Classical.choice", "Quot.sound", "propext"]
    print(json.dumps({"status": "PASS", "live": args.live, "local_pins": len(manifest["files"]), "root_pins": len(pins), "lean_jobs": 3, "failed_checks": 1, "warning_checks": 0, "canonical_jobs": 0, "infrastructure_attempts": 0, "constructed_pairs": 0, "new_public_pairs": 1, "public_heads": [HEAD], "all_eight_settings": True, "public_type_identity": True, "standard_axioms_only": True, "manifest_sha256": sha(HERE / (PREFIX + "manifest.json"))}, indent=2))

if __name__ == "__main__":
    main()
