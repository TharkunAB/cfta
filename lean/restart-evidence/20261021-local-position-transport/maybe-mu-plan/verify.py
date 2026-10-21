#!/usr/bin/env python3
"""Check the source-only design package and its pinned source files."""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent

def check(path: Path, pin: dict) -> None:
    data = path.read_bytes()
    assert len(data) == pin['bytes'], f'byte count: {path}'
    assert hashlib.sha256(data).hexdigest() == pin['sha256'], f'sha256: {path}'

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE / 'manifest.json').read_text())
    for pin in manifest['files']:
        check(HERE / pin['path'], pin)
    pins = json.loads((HERE / 'source-pins.json').read_text())
    for pin in pins['files']:
        check(HERE / 'inputs/root' / pin['path'], pin)
        if args.live:
            check(args.root / pin['path'], pin)
    assert manifest['lean_jobs'] == 0
    assert manifest['new_proof_pairs'] == 0
    report = (HERE / 'plan.md').read_text()
    for term in ['NativeConstructReadback.construct', 'unproved', 'MuStored', 'PlainDomain',
                 '250', 'arbitrary-view', 'termination']:
        assert term in report, term
    assert not list(HERE.glob('*-direct-*.json'))
    print(json.dumps({'status': 'PASS', 'local_pins': len(manifest['files']),
                      'root_sources': len(pins['files']), 'live': args.live,
                      'lean_jobs': 0, 'new_proof_pairs': 0}, sort_keys=True))

if __name__ == '__main__':
    main()
