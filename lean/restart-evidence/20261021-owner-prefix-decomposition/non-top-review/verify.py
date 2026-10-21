#!/usr/bin/env python3
"""Verify source-only non-Top contract audit pins."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def safe(value: str) -> Path:
    path = Path(value)
    assert not path.is_absolute() and '..' not in path.parts
    return path


def check(path: Path, pin: dict) -> None:
    assert path.is_file() and path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256'], str(path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = read(here / 'manifest.json')
    assert manifest['finalized']
    for pin in manifest['files']:
        check(here / safe(pin['path']), pin)
    sources = read(here / 'source-pins.json')['sources']
    assert sources == manifest['sources'] and len(sources) == 6
    for pin in sources:
        snapshot = here / safe(pin['snapshot'])
        check(snapshot, pin)
        lines = snapshot.read_bytes().splitlines(keepends=True)
        assert len(lines) == pin['lines']
        for span in pin['reviewed_ranges']:
            lo, hi = span['start'], span['end']
            assert 1 <= lo <= hi <= len(lines)
            assert hashlib.sha256(b''.join(lines[lo - 1:hi])).hexdigest() == span['sha256']
        if args.live:
            check(args.root / safe(pin['path']), pin)
    scope = read(here / 'scope.json')
    assert scope['status'] == 'SOURCE_ONLY_UNPROVED' and scope['core_source_files'] == 6
    for key in ['lean_jobs', 'runtime_jobs', 'canonical_jobs', 'public_pairs', 'official_edits', 'new_theorems_claimed', 'counterexamples_claimed']:
        assert scope[key] == 0
    assert sha(here / 'inputs/frontier/next-contract.lean.txt') == scope['source_contract_sha256']
    assert scope['complete_proposed_plan_reviewed'] and scope['complete_two_head_types_reviewed']
    assert sha(here / 'inputs/geometry-plan/plan.md') == scope['plan_sha256']
    assert sha(here / 'inputs/geometry-plan/proposed-signature.lean.txt') == scope['proposed_types_sha256']
    report = (here / 'report.md').read_text()
    assert 'That route remains unproved.' in report
    assert 'No actual counterexample was established.' in report
    assert 'Authorship:' in report and 'Prefix decomposition is assigned separately.' in report
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']), 'root_pins': len(sources), 'lean_jobs': 0, 'native_runtime_jobs': 0, 'canonical_jobs': 0, 'public_pairs': 0, 'new_theorems_claimed': 0, 'counterexamples_claimed': 0, 'manifest_sha256': sha(here / 'manifest.json')}, indent=2))


if __name__ == '__main__':
    main()
