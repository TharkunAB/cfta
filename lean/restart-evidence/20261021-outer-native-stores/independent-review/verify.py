#!/usr/bin/env python3
"""Check the independent completed-outer review without running Lean."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = "SourceCurrentOuterNativeStores.lean"
FINAL = "b9f7f87df92990b460708bd71fb5f56085bc3b28b97c0a0d96ae1e12f6156f46"
HEADS = ["MicroCFTA.SourceCurrentOuterNativeStores." + name
         for name in ("edge_call", "node_call", "descendants")]


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def check(path: Path, pin: dict) -> None:
    data = path.read_bytes()
    assert len(data) == pin["bytes"] and digest(data) == pin["sha256"], str(path)


def relative(value: str) -> Path:
    path = Path(value)
    assert not path.is_absolute() and ".." not in path.parts, value
    return path


def normalized(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text())
    assert manifest["finalized"] and manifest["independent_review"]
    assert manifest["owned_lean_lake_commands"] == manifest["owned_public_pairs"] == 0
    for pin in manifest["files"]:
        check(HERE / relative(pin["path"]), pin)
    pins = json.loads((HERE / "source-pins.json").read_text())["sources"]
    assert pins == manifest["sources"]
    for pin in pins:
        snapshot = HERE / relative(pin["snapshot"])
        check(snapshot, pin)
        lines = snapshot.read_bytes().splitlines(keepends=True)
        for span in pin["reviewed_ranges"]:
            lo, hi = span["start"], span["end"]
            assert 1 <= lo <= hi <= len(lines)
            assert digest(b"".join(lines[lo-1:hi])) == span["sha256"]
        if args.live:
            check(args.root / relative(pin["path"]), pin)

    owner = HERE / "inputs/owner"
    selected = json.loads((owner / "outer-native-stores-selection.json").read_text())
    assert selected["source_sha256"] == FINAL
    assert selected["lean_jobs"] == 5 and selected["failed_checks"] == 3
    assert selected["infrastructure_attempts"] == selected["canonical_jobs"] == 0
    assert selected["new_public_pairs"] == 3 and selected["constructed_pairs"] == 0
    assert selected["failed_checks_with_warning_diagnostics"] == ["outer-native-stores-direct-2"]
    assert selected["warning_success_checks"] == 0
    source = (owner / SOURCE).read_text()
    assert digest(source.encode()) == FINAL and len(source.splitlines()) == 528
    assert re.findall(r"^theorem (\w+)", source, re.M) == ["edge_call", "node_call", "descendants"]
    assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private", source)
    proposal = (HERE / "inputs/audit/proposed-signature.lean.txt").read_text()
    for name in ("edge_call", "node_call", "descendants"):
        public = source.split("theorem " + name + "\n", 1)[1].split(" := by", 1)[0]
        expected = proposal.split("theorem " + name + "\n", 1)[1]
        expected = expected.split("\n\n", 1)[0].split("\nend MicroCFTA.", 1)[0]
        assert public.rstrip() == expected.rstrip(), name
    assert digest((owner / "outer-native-stores-prelaunch-1.source.lean").read_bytes()) == "37fd18215d0a6c59aeaa77e7f3b1254822587f0063b5df89b18b359b0607dcb2"
    assert not (owner / "outer-native-stores-direct-4.log").read_bytes()
    assert (owner / "outer-native-stores-direct-4.source.lean").read_text() == source
    raw = (owner / "outer-native-stores-public-1.log").read_bytes()
    assert len(raw) == 188492 and digest(raw) == "d999ea714584b13639dd1119849f818dbc05f0d7bee82873219d2fb9cf026606"
    log = raw.decode()
    assert not re.search(r"sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.", log)
    printer = (owner / "outer-native-stores-public-1.source.lean").read_text()
    assert printer.startswith(source + "\n")
    for option in ("linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true",
                   "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"):
        assert printer.count("set_option " + option) == 1, option
    for head in HEADS:
        checked, tail = log.split("@" + head + " :", 1)[1].split("\ntheorem " + head, 1)
        typed, proof = tail.split(" :=", 1)
        assert normalized(checked) == normalized(typed.removeprefix(" :")), head
        assert "_private" not in checked + typed and "Stores" not in checked + typed
        assert len(proof) > 100
        match = re.search(re.escape("'" + head + "' depends on axioms:") + r"\s*\[([^\]]*)\]", log)
        assert match, head
        axioms = {re.sub(r"\.\{[^}]*\}", "", item.strip()) for item in match.group(1).split(",")}
        assert axioms == {"propext", "Classical.choice", "Quot.sound"}, head
        for command in ("#check @", "#print ", "#print axioms "):
            assert printer.count(command + head + "\n") == 1

    command = [sys.executable, str(owner / "outer-native-stores-verify.py"), "--root", str(args.root)]
    if args.live:
        command.append("--live")
    checked = subprocess.run(command, cwd="/", env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"),
                             capture_output=True, text=True)
    assert checked.returncode == 0, (checked.stdout, checked.stderr)
    owner_result = json.loads(checked.stdout)
    assert owner_result["status"] == "PASS"
    print(json.dumps({"status": "PASS", "live": args.live, "local_pins": len(manifest["files"]),
                      "root_pins": len(pins), "owned_lean_lake_commands": 0, "owned_public_pairs": 0,
                      "reused_lean_jobs": 5, "reused_failed_checks": 3,
                      "reused_warning_bearing_failed_checks": 1, "reused_canonical_jobs": 0,
                      "reused_public_pairs": 3, "material_open_issues": 0,
                      "full_public_log_bytes": len(raw), "all_public_type_identities": True,
                      "all_eight_printer_settings": True, "standard_axioms_each_head": True,
                      "authored_general_parent_foundation_disclosed": True,
                      "manifest_sha256": digest((HERE / "manifest.json").read_bytes()),
                      "frozen_owner_checker": owner_result}, indent=2))


if __name__ == "__main__":
    main()
