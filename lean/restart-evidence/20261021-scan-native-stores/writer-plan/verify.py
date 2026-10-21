#!/usr/bin/env python3
"""Check the source-only Parent writer plan and its frozen snapshots."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / 'manifest.json').read_text())
    for pin in manifest['files']:
        path = Path(pin['path'])
        assert not path.is_absolute() and '..' not in path.parts
        current = here / path
        assert current.stat().st_size == pin['bytes'] and digest(current) == pin['sha256'], str(path)
    pins = json.loads((here / 'source-pins.json').read_text())
    assert manifest['sources'] == pins['sources']
    assert not pins['official_edits'] and not pins['implementation_authorized']
    assert pins['new_lean_commands'] == pins['new_lake_commands'] == pins['new_canonical_commands'] == 0
    for pin in pins['sources']:
        path, snapshot = Path(pin['path']), Path(pin['snapshot'])
        assert not path.is_absolute() and '..' not in path.parts
        assert not snapshot.is_absolute() and '..' not in snapshot.parts
        current = here / snapshot
        assert current.stat().st_size == pin['bytes'] and digest(current) == pin['sha256'], str(path)
        lines = current.read_bytes().splitlines(keepends=True)
        for span in pin['reviewed_ranges']:
            start, end = span['start'], span['end']
            assert 1 <= start <= end <= len(lines)
            assert hashlib.sha256(b''.join(lines[start - 1:end])).hexdigest() == span['sha256']
        if args.live:
            assert digest(args.root / path) == pin['sha256'], str(path)
    draft = pins['draft']
    assert digest(here / draft['path']) == draft['sha256']
    assert (here / draft['path']).stat().st_size == draft['bytes']
    plan = (here / 'plan.md').read_text()
    for text in ['SOURCE-ONLY PLAN', 'same existential', 'physical admission', 'machine-width contract',
                 'rows_tail', 'walk_tail', 'not derive past facts', 'No theorem in this plan was proved']:
        assert text in plan, text
    print(json.dumps({'status': 'PASS', 'live': args.live, 'root_sources': len(pins['sources']),
                      'local_pins': len(manifest['files']), 'new_lean_commands': 0,
                      'new_lake_commands': 0, 'new_canonical_commands': 0,
                      'proposed_claim_proved': False,
                      'manifest_sha256': digest(here / 'manifest.json')}, indent=2))


if __name__ == '__main__':
    main()
