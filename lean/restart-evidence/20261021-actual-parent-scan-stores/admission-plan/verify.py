#!/usr/bin/env python3
"""Check the frozen local Parent Scan source plan."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative(value: str) -> Path:
    path = Path(value)
    assert not path.is_absolute() and '..' not in path.parts
    return path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / 'manifest.json').read_text())
    for pin in manifest['files']:
        current = here / relative(pin['path'])
        assert current.stat().st_size == pin['bytes'] and digest(current) == pin['sha256'], pin['path']
    pins = json.loads((here / 'source-pins.json').read_text())
    assert manifest['sources'] == pins['sources']
    assert not pins['official_edits'] and not pins['proposed_claim_proved']
    assert pins['draft_authorized'] and not pins['proof_launch_authorized']
    assert pins['new_lean_commands'] == pins['new_lake_commands'] == pins['new_canonical_commands'] == 0
    for pin in pins['sources']:
        current = here / relative(pin['snapshot'])
        assert current.stat().st_size == pin['bytes'] and digest(current) == pin['sha256'], pin['path']
        lines = current.read_bytes().splitlines(keepends=True)
        for span in pin['reviewed_ranges']:
            lo, hi = span['start'], span['end']
            assert 1 <= lo <= hi <= len(lines)
            assert hashlib.sha256(b''.join(lines[lo - 1:hi])).hexdigest() == span['sha256']
        if args.live:
            assert digest(args.root / relative(pin['path'])) == pin['sha256'], pin['path']
    print(json.dumps({'status':'PASS','live':args.live,'source_pins':len(pins['sources']),
                      'local_pins':len(manifest['files']),'new_lean_commands':0,'proposed_claim_proved':False,
                      'manifest_sha256':digest(here/'manifest.json')},indent=2))


if __name__ == '__main__':
    main()
