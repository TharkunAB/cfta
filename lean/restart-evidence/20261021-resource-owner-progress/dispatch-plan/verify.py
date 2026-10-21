#!/usr/bin/env python3
"""Verify the source-only immediate dispatch plan without running Lean."""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def relative(value: str) -> Path:
    path = Path(value)
    assert not path.is_absolute() and ".." not in path.parts, value
    return path

def check(path: Path, pin: dict) -> None:
    assert path.is_file() and path.stat().st_size == pin["bytes"] and digest(path) == pin["sha256"], str(path)

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--live", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((HERE / "manifest.json").read_text())
    assert manifest["finalized"] and manifest["component"] == "source-only immediate Top-owner dispatch plan"
    assert manifest["lean_jobs"] == manifest["canonical_jobs"] == manifest["public_pairs"] == 0
    assert manifest["official_edits"] is False
    for pin in manifest["files"]:
        check(HERE / relative(pin["path"]), pin)
    sources = json.loads((HERE / "source-pins.json").read_text())["sources"]
    assert sources == manifest["sources"] and len(sources) == 13
    for pin in sources:
        snapshot = HERE / relative(pin["snapshot"])
        check(snapshot, pin)
        lines = snapshot.read_bytes().splitlines(keepends=True)
        assert len(lines) == pin["lines"]
        for span in pin["reviewed_ranges"]:
            lo, hi = span["start"], span["end"]
            assert 1 <= lo <= hi <= len(lines)
            assert hashlib.sha256(b"".join(lines[lo-1:hi])).hexdigest() == span["sha256"]
        if args.live:
            check(args.root / relative(pin["path"]), pin)
    proposal = (HERE / "proposed-signature.lean.txt").read_text()
    assert re.findall(r"^theorem (\w+)", proposal, re.M) == ["key_ne_top"]
    assert "namespace MicroCFTA.SourceCurrentResourceOwnerDispatch" in proposal
    assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|:= by|_private", proposal)
    assert "(member : original ∈ ownerRows)" in proposal
    assert "(active : before.nodeResults.cells handle = some" in proposal
    assert "parented.children.take slot" in proposal and "parented.children[slot]? = some value" in proposal
    assert "(positiveMemo : SourceCurrentMergePositivePosition.Support" in proposal
    pending = json.loads((HERE / "pending-consumer-contract.json").read_text())
    assert pending["declaration"] == "MicroCFTA.SourceCurrentResourceOwnerProgress.key_ne_top"
    assert pending["proof_jobs_owned_by_this_plan"] == 0 and pending["live_source_pin"] is False
    assert digest(HERE / relative(pending["snapshot"])) == pending["sha256"]
    assert "pending proof check" in pending["status_at_drafting"]
    summary = json.loads((HERE / "dependency-checked-readback.json").read_text())
    assert summary["status"] == "CHECKED dependency" and summary["jobs_owned_by_plan"] == 0
    assert summary["source_sha256"] == "05b2dd2001743235a81a5190060e28bd61fdd1a044ecb2476096de85e2c11a0e"
    dependency = HERE / "inputs/dependency"
    assert digest(dependency / "resource-owner-progress-manifest.json") == summary["owner_manifest_sha256"]
    selected = json.loads((dependency / "resource-owner-progress-selection.json").read_text())
    assert selected["source_sha256"] == summary["source_sha256"]
    strict, public = selected["selected_strict"], selected["selected_public"]
    for stem in (strict, public):
        assert json.loads((dependency / (stem + ".json")).read_text())["exit_code"] == 0
        assert json.loads((dependency / (stem + ".limits.json")).read_text()) == {"memory.max": "4294967296", "memory.high": "4294967296", "memory.swap.max": "0"}
    assert not (dependency / (strict + ".log")).read_bytes()
    assert digest(dependency / (strict + ".source.lean")) == summary["source_sha256"]
    log_path = dependency / (public + ".log")
    assert log_path.stat().st_size == summary["public_log_bytes"] == 10187067
    assert digest(log_path) == summary["public_log_sha256"] == "024db855722d5722e41d31828886790f03b71336e39d3bf15e93a2b6630f827c"
    log = log_path.read_text()
    assert not re.search(r"sorryAx|\b(?:error|warning)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|\.\.\.|⋯|…", log)
    head = summary["declaration"]
    checked, printed = log.split("@" + head + " :", 1)[1].split("\ntheorem " + head + " :", 1)
    boundaries = list(re.finditer(r" :=\n(?=fun\b)", printed))
    assert len(boundaries) == 1
    boundary = boundaries[0]
    declared, proof = printed[:boundary.start()], printed[boundary.end():]
    assert "".join(checked.split()) == "".join(declared.split())
    assert "_private" not in checked + declared and len(proof) > 1000
    printer = (dependency / (public + ".source.lean")).read_text()
    for option in ("linter.all true", "pp.explicit true", "pp.fullNames true", "pp.proofs true", "pp.proofs.threshold 254", "pp.universes true", "pp.deepTerms true", "pp.maxSteps 10000000"):
        assert printer.count("set_option " + option) == 1
    match = re.search(re.escape("'" + head + "' depends on axioms:") + r"\s*\[([^\]]*)\]", proof)
    assert match
    axioms = sorted(item.strip() for item in re.sub(r"\.\{[^}]*\}", "", match.group(1)).split(","))
    assert axioms == summary["axioms"] == ["Classical.choice", "Quot.sound", "propext"]
    assert "pending dependency" in (HERE / "draft-pending-plan.md").read_text()
    assert "now checked and installed" in (HERE / "plan.md").read_text()
    assert not list(HERE.glob("*.olean")) and not list(HERE.glob("*.log"))
    print(json.dumps({"status": "PASS", "live": args.live, "local_pins": len(manifest["files"]),
                      "root_pins": len(sources), "source_ranges": sum(len(p["reviewed_ranges"]) for p in sources),
                      "lean_jobs": 0, "canonical_jobs": 0, "public_pairs": 0,
                      "proposed_public_head": "MicroCFTA.SourceCurrentResourceOwnerDispatch.key_ne_top",
                      "manifest_sha256": digest(HERE / "manifest.json")}, indent=2))

if __name__ == "__main__":
    main()
