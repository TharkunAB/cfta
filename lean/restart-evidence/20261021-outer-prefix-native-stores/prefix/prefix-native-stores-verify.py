#!/usr/bin/env python3
"""Verify the frozen unfinished-prefix store proof without running Lean."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
HEAD = "MicroCFTA.SourceCurrentOuterPrefixNativeStores.reached"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def relative(value: str) -> Path:
    result = Path(value)
    assert not result.is_absolute() and ".." not in result.parts, value
    return result


def check(path: Path, pin: dict) -> None:
    assert path.is_file() and path.stat().st_size == pin["bytes"] and digest(path) == pin["sha256"], str(path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    manifest = read(HERE / "prefix-native-stores-manifest.json")
    assert manifest["finalized"]
    for pin in manifest["files"]:
        check(HERE / relative(pin["path"]), pin)
    sources = read(HERE / "prefix-native-stores-source-pins.json")["files"]
    assert sources == manifest["sources"]
    for pin in sources:
        snapshot = HERE / relative(pin["snapshot"])
        check(snapshot, pin)
        lines = snapshot.read_bytes().splitlines(keepends=True)
        for span in pin["reviewed_ranges"]:
            lo, hi = span["start"], span["end"]
            assert 1 <= lo <= hi <= len(lines)
            assert hashlib.sha256(b"".join(lines[lo-1:hi])).hexdigest() == span["sha256"]
        if args.live:
            check(args.root / relative(pin["path"]), pin)
    selected = read(HERE / "prefix-native-stores-selection.json")
    assert selected["finalized"] and selected["public_heads"] == [HEAD]
    assert selected["lean_jobs"] == 3 and selected["failed_checks"] == 1
    assert selected["infrastructure_attempts"] == selected["canonical_jobs"] == selected["constructed_pairs"] == 0
    assert selected["new_public_pairs"] == 1 and selected["warning_success_checks"] == 0
    assert selected["failed_checks_with_warning_diagnostics"] == []
    source = HERE / selected["source"]
    assert digest(source) == selected["source_sha256"] == "7e1d2349590e0cdd9ad3028e3b25ca1a2d44502766663551fcf901a185a4e1d8"
    text = source.read_text()
    assert len(text.splitlines()) == selected["source_lines"] == 198
    assert re.findall(r"^theorem (\w+)", text, re.M) == ["reached"]
    assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private", text)
    proposal = (HERE / "inputs/plan/proposed-signature.lean.txt").read_text()
    assert text.split("theorem reached\n", 1)[1].split(" := by", 1)[0] == proposal.split("theorem reached\n", 1)[1].split("\nend MicroCFTA.", 1)[0]
    assert selected["public_header_matches_frozen_proposal"]
    assert "open SourceCurrentOuterExecutionAncestry (Step Reached)" in text
    assert "SourceCurrentOuterActiveAncestry.Reached" not in text
    assert text.count("SourceCurrentOuterInitialPrefix.reached formulas solver seed") == 2
    assert text.count("SourceCurrentOuterNativeStores.edge_call formulas solver") == 2
    assert text.count("SourceCurrentOuterNativeStores.descendants formulas solver") == 1
    assert text.count("SourceCurrentOuterNativeStores.node_call formulas solver") == 1
    ledger = read(HERE / "prefix-native-stores-attempt-ledger.json")
    assert ledger["infrastructure_attempts"] == []
    attempts = ledger["attempts"]
    assert len(attempts) == len({item["name"] for item in attempts}) == 3
    failed = 0
    for item in attempts:
        stem = item["name"]
        receipt = read(HERE / (stem + ".json"))
        assert item["lean_launched"] and receipt["exit_code"] == item["exit_code"]
        assert digest(HERE / receipt["source"]) == receipt["sha256"] == item["source_sha256"]
        assert receipt["source"] == stem + ".source.lean" and receipt["log"] == stem + ".log"
        assert digest(HERE / (stem + ".json")) == item["receipt_sha256"]
        assert digest(HERE / (stem + ".log")) == item["log_sha256"]
        assert read(HERE / (stem + ".limits.json")) == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
        usage = read(HERE / (stem + ".usage.json"))
        assert 0 <= usage["age_seconds"] < 120 and usage["remaining_percent"] > 1
        assert usage["remaining_percent"] == item["usage_remaining_percent"]
        assert "--mem" in receipt["wrapper"] and "4G" in receipt["wrapper"]
        assert "--time" in receipt["wrapper"] and "5m" in receipt["wrapper"]
        assert "-Dlinter.all=true" in receipt["command"]
        assert "lean4---v4.34.1/bin/lean" in receipt["command"][0]
        log = (HERE / (stem + ".log")).read_text()
        assert item["warning_diagnostics"] == len(re.findall(r": warning:", log)) == 0
        failed += receipt["exit_code"] != 0
    assert failed == 1
    strict, public = selected["selected_strict"], selected["selected_public"]
    assert read(HERE / (strict + ".json"))["exit_code"] == read(HERE / (public + ".json"))["exit_code"] == 0
    assert not (HERE / (strict + ".log")).read_bytes()
    assert (HERE / (strict + ".source.lean")).read_bytes() == source.read_bytes()
    full = HERE / (public + ".log")
    assert full.stat().st_size == selected["public_log_bytes"] == 1328359
    assert digest(full) == selected["public_log_sha256"] == "724f20ee3132dabaa1f62a0b243c6969d2b8cb001e47c507bf2f9e5e03670231"
    log = full.read_text()
    assert not re.search(r"sorryAx|\b(?:error|warning)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|\.\.\.|⋯|…", log)
    printer = (HERE / (public + ".source.lean")).read_text()
    assert printer.startswith(text + "\n")
    for option in ("linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"):
        assert printer.count("set_option " + option) == 1
    checked, declared = log.split("@" + HEAD + " :", 1)[1].split("\ntheorem " + HEAD, 1)
    declared, proof = declared.split(" :=", 1)
    assert "".join(checked.split()) == "".join(declared.removeprefix(" :").split())
    assert "_private" not in checked + declared and "Stores" not in checked + declared
    assert len(proof) > 1000
    match = re.search(re.escape("'" + HEAD + "' depends on axioms:") + r"\s*\[([^\]]*)\]", log)
    assert match
    names = sorted(item.strip() for item in re.sub(r"\.\{[^}]*\}", "", match.group(1)).split(","))
    assert names == selected["axioms_by_head"][HEAD] == ["Classical.choice", "Quot.sound", "propext"]
    for command in ("#check @", "#print ", "#print axioms "):
        assert printer.count(command + HEAD + "\n") == 1
    assert read(HERE / "prelaunch-mechanical-delta.json")["lean_lake_canonical_commands"] == 0
    assert digest(HERE / "prefix-native-stores-prelaunch-1.source.lean") == "0c839a345b1c1f97d99d33f935611ec9c0fc47d56c7bc01f5d3b02179ba334bd"
    assert (HERE / "prefix-native-stores-direct-1.log").read_text().count("Unknown identifier `stores`") == 5
    print(json.dumps({"status": "PASS", "live": args.live, "local_pins": len(manifest["files"]),
                      "root_pins": len(sources), "lean_jobs": 3, "failed_checks": 1,
                      "warning_success_checks": 0, "canonical_jobs": 0, "infrastructure_attempts": 0,
                      "constructed_pairs": 0, "new_public_pairs": 1, "public_heads": [HEAD],
                      "standard_axioms_only": True, "all_eight_printer_settings": True,
                      "public_type_identity": True, "manifest_sha256": digest(HERE / "prefix-native-stores-manifest.json")}, indent=2))


if __name__ == "__main__":
    main()
