#!/usr/bin/env python3
"""Check the gate/conjunction interval plan and its pinned source ranges."""
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
    for entry in manifest['files']:
        path = Path(entry['path'])
        assert not path.is_absolute() and '..' not in path.parts
        data = (here / path).read_bytes()
        assert len(data) == entry['bytes'] and sha(data) == entry['sha256'], str(path)
    pins = json.loads((here / 'source-pins.json').read_text())
    assert pins['sources'] == manifest['sources']
    ranges = []
    for source in pins['sources']:
        path, snapshot = Path(source['path']), Path(source['snapshot'])
        assert not path.is_absolute() and '..' not in path.parts
        assert not snapshot.is_absolute() and '..' not in snapshot.parts
        data = (here / snapshot).read_bytes()
        assert len(data) == source['bytes'] and sha(data) == source['sha256'], str(path)
        lines = data.splitlines(keepends=True)
        for span in source['reviewed_ranges']:
            start, end = span['start'], span['end']
            assert 1 <= start <= end <= len(lines)
            assert sha(b''.join(lines[start - 1:end])) == span['sha256']
            ranges.append({'path': source['path'], **span})
        if args.live:
            assert sha((args.root / path).read_bytes()) == source['sha256'], str(path)
    assert ranges == json.loads((here / 'ranges.json').read_text())['ranges']
    selection = json.loads((here / 'selection.json').read_text())
    assert selection['finalized'] and not selection['proposed_result_proved']
    assert not selection['official_edits'] and not selection['implementation_authorized_in_this_package']
    assert selection['proposed_public_heads'] == [
        'SourceCurrentGatePublicationHistory.primary',
        'SourceCurrentGatePublicationHistory.secondary',
        'SourceCurrentConjunctionPublicationHistory.call',
    ]
    assert not selection['old_native_whole_file_pinned']
    assert not any(item['path'].endswith('/SourceCurrentNativeRequestPositivePositions.lean') for item in pins['sources'])
    for field in ('new_lean_commands', 'new_canonical_commands', 'new_public_pairs', 'new_constructed_pairs'):
        assert pins[field] == selection[field] == 0
    dependency = pins['next_dependency']
    assert sha((here / dependency['append_snapshot']).read_bytes()) == dependency['append_sha256']
    current = next(item for item in pins['sources'] if item['path'].endswith('/SourceCurrentNativeCurrentStores.lean'))
    assert current['sha256'] == dependency['current_stores_sha256']
    plan = (here / 'plan.md').read_text()
    for clause in (
        'SOURCE-ONLY PLAN', 'The proposed interval heads are unproved.',
        'primary TRUE and secondary FALSE', 'It does not prove result closure.',
        'Scoped', 'WordRanges', 'No public theorem for that conversion was found',
        'does NOT whole-file live-pin old', 'exact physical state',
    ):
        assert clause in plan, clause
    signature = (here / 'proposed-signatures.lean.txt').read_text()
    for head in ('primary', 'secondary', 'call'):
        assert signature.count('theorem ' + head) == 1
    assert 'before answer after' in signature and 'before.heap after.heap' in signature
    assert 'Cap Plain' not in signature and '(causal :' not in signature
    print(json.dumps({
        'status': 'PASS', 'live': args.live,
        'root_sources': len(pins['sources']), 'reviewed_ranges': len(ranges),
        'pins': len(manifest['files']) + len(manifest['sources']),
        'new_lean_commands': 0, 'new_canonical_commands': 0,
        'new_public_pairs': 0, 'new_constructed_pairs': 0,
        'proposal_proved': False, 'scope': 'actual gate/conjunction intervals, separate seeded closure requirement',
        'manifest_sha256': sha((here / 'manifest.json').read_bytes()),
    }, indent=2))


if __name__ == '__main__':
    main()
