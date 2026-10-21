#!/usr/bin/env python3
"""Check the source-only Scan store plan and its exact source ranges."""
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
    assert not selection['official_edits'] and not selection['implementation_authorized_in_this_task']
    assert selection['proposed_public_heads'] == [
        'SourceCurrentNativeRequestPositivePositions.call_stores',
        'SourceCurrentNativeCurrentStores.step',
    ]
    for field in ('new_lean_commands', 'new_canonical_commands', 'new_public_pairs', 'new_constructed_pairs'):
        assert pins[field] == selection[field] == 0
    baseline = next(item for item in pins['sources'] if item['path'].endswith('/SourceCurrentNativeRequestPositivePositions.lean'))
    assert baseline['sha256'] == selection['archived_baseline_sha256']
    assert len((here / baseline['snapshot']).read_bytes().splitlines()) == 1193
    plan = (here / 'plan.md').read_text()
    for clause in (
        'SOURCE-ONLY PLAN', 'The two proposed endpoints are unproved public additions.',
        'PRIMARY returns TRUE and SECONDARY returns FALSE',
        'Exact operand availability and closure remain explicit.',
        'conditional', 'The proposed wrapper does not claim result closure.',
        'original 1193-line', 'an old whole-source live pin cannot also match the new file',
        'No copied 1100-line native induction',
    ):
        assert clause in plan, clause
    signature = (here / 'proposed-signatures.lean.txt').read_text()
    assert signature.count('theorem call_stores') == signature.count('theorem step') == 1
    assert '(leftClosed : left.free = []) (rightClosed : right.free = [])' in signature
    assert 'CheckedJointInduction.Return' in signature and 'CheckedJointCode.NodeLaw' in signature
    assert '(leftCap :' not in signature and '(rightCap :' not in signature
    assert 'PositiveAt result' not in signature
    print(json.dumps({
        'status': 'PASS', 'live': args.live,
        'root_sources': len(pins['sources']), 'reviewed_ranges': len(ranges),
        'pins': len(manifest['files']) + len(manifest['sources']),
        'new_lean_commands': 0, 'new_canonical_commands': 0,
        'new_public_pairs': 0, 'new_constructed_pairs': 0,
        'proposal_proved': False, 'scope': 'caps-free conditional query stores only',
        'manifest_sha256': sha((here / 'manifest.json').read_bytes()),
    }, indent=2))


if __name__ == '__main__':
    main()
