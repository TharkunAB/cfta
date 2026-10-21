#!/usr/bin/env python3
"""Check the source-only completed-trace scope plan."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / 'manifest.json').read_text())
    for item in manifest['files']:
        path = Path(item['path'])
        assert not path.is_absolute() and '..' not in path.parts
        data = (here / path).read_bytes()
        assert len(data) == item['bytes'] and sha(data) == item['sha256'], str(path)
    pins = json.loads((here / 'source-pins.json').read_text())
    assert pins['sources'] == manifest['sources']
    for item in pins['sources']:
        path, snapshot = Path(item['path']), Path(item['snapshot'])
        assert not path.is_absolute() and '..' not in path.parts
        assert not snapshot.is_absolute() and '..' not in snapshot.parts
        data = (here / snapshot).read_bytes()
        assert len(data) == item['bytes'] and sha(data) == item['sha256'], str(path)
        lines = data.splitlines(keepends=True)
        for span in item['reviewed_ranges']:
            start, end = span['start'], span['end']
            assert 1 <= start <= end <= len(lines)
            assert sha(b''.join(lines[start - 1:end])) == span['sha256']
        if args.live:
            assert sha((args.root / path).read_bytes()) == item['sha256'], str(path)
    selected = json.loads((here / 'selection.json').read_text())
    assert selected['finalized'] and not selected['proved'] and not selected['official_edits']
    for field in ('new_lean_commands', 'new_lake_commands', 'new_canonical_commands', 'new_public_pairs', 'new_constructed_pairs'):
        assert pins[field] == selected[field] == 0
    assert selected['proposed_public_heads'] == ['word_ranges', 'step']
    plan = (here / 'plan.md').read_text()
    for text in ('SOURCE-ONLY PLAN', 'SourceEqualityNativeDemand.Steps', 'not the raw',
                 'Step.unique', 'Scoped', 'Idle', 'does not remove', 'zero new Lean'):
        assert text in plan, text
    print(json.dumps({'status': 'PASS', 'live': args.live, 'root_sources': len(pins['sources']),
                     'pins': len(manifest['files']) + len(manifest['sources']),
                     'new_lean_commands': 0, 'new_lake_commands': 0, 'new_canonical_commands': 0,
                     'proved': False, 'manifest_sha256': sha((here / 'manifest.json').read_bytes())}, indent=2))


if __name__ == '__main__':
    main()
