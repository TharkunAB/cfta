#!/usr/bin/env python3
"""Verify exact source snapshots for the unproved class observation plan."""
import argparse
import hashlib
import json
from pathlib import Path


def check(path: Path, pin: dict) -> None:
    data = path.read_bytes()
    assert len(data) == pin['bytes'], str(path)
    assert hashlib.sha256(data).hexdigest() == pin['sha256'], str(path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / 'plan-manifest.json').read_text())
    for pin in manifest['files']:
        check(here / pin['path'], pin)
    sources = json.loads((here / 'plan-source-pins.json').read_text())
    for pin in sources['files']:
        check(here / 'inputs/root' / pin['path'], pin)
        if args.live:
            check(args.root / pin['path'], pin)
    for pin in sources['candidates']:
        check(here / pin['path'], pin)
    assert manifest['lean_jobs'] == manifest['new_proof_pairs'] == manifest['constructed_examples'] == 0
    assert not list(here.glob('*-direct-*.json'))
    report = (here / 'plan.md').read_text()
    for phrase in ['unproved', 'RowPositive', 'path ++ residual', 'nullary',
                   'SAME native continuation', 'Force.hit', 'phaseValues', 'ORIGINAL',
                   'opaque-Mu counterexample', 'captured Origins', 'global runtime rank']:
        assert phrase in report, phrase
    print(json.dumps({'status': 'PASS', 'live': args.live,
                      'local_pins': len(manifest['files']), 'root_sources': len(sources['files']),
                      'candidate_sources': len(sources['candidates']), 'lean_jobs': 0,
                      'new_proof_pairs': 0, 'constructed_examples': 0}, sort_keys=True))


if __name__ == '__main__':
    main()
