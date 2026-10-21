#!/usr/bin/env python3
"""Verify the completed outer store audit without running Lean."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def relative(value: str) -> Path:
    path = Path(value)
    assert not path.is_absolute() and '..' not in path.parts, value
    return path


def check(path: Path, pin: dict) -> bytes:
    data = path.read_bytes()
    assert len(data) == pin['bytes'] and sha(data) == pin['sha256'], str(path)
    return data


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = json.loads((here / 'audit-manifest.json').read_text())
    assert manifest['finalized'] and manifest['source_only']
    for pin in manifest['files']:
        check(here / relative(pin['path']), pin)
    pins = json.loads((here / 'audit-source-pins.json').read_text())['files']
    assert pins == manifest['sources']
    for pin in pins:
        data = check(here / 'inputs/root' / relative(pin['path']), pin)
        lines = data.splitlines(keepends=True)
        assert len(lines) == pin['lines']
        for cut in pin['reviewed_ranges']:
            assert 1 <= cut['first'] <= cut['last'] <= len(lines)
            fragment = b''.join(lines[cut['first']-1:cut['last']])
            assert sha(fragment) == cut['sha256']
        if args.live:
            check(args.root / relative(pin['path']), pin)
    selected = json.loads((here / 'audit-selection.json').read_text())
    assert selected['finalized'] and selected['source_only']
    assert all(selected[key] == 0 for key in [
        'new_lean_commands', 'new_lake_commands', 'new_canonical_commands',
        'owned_public_pairs', 'constructed_pairs', 'reused_proof_commands'])
    assert not selected['official_edits'] and not selected['proposed_heads_checked']
    assert selected['normality_already_proved'] and selected['prefix_resources_already_proved']
    assert selected['proposed_public_heads'] == ['edge_call', 'node_call', 'descendants']
    assert selected['private_induction_phases'] == [
        'node_call', 'node_body', 'rows', 'descendants', 'children', 'walk']
    assert selected['unchanged_native_support_author_disclosed']
    report = (here / 'report.md').read_text()
    for phrase in [
        'SAME numeric receipt', 'Existing unfinished-prefix producer',
        'ONE existential writer entry', 'ENTIRE caller',
        'does not assert that every cached input', 'zero Lean',
        'do not reconstruct their full receipts']:
        assert phrase.lower() in report.lower(), phrase
    proposed = (here / 'proposed-signature.lean.txt').read_text()
    for head in selected['proposed_public_heads']:
        assert proposed.count('theorem ' + head + '\n') == 1
    assert 'PROPOSED INTERFACE ONLY' in proposed and ':= by' not in proposed
    assert 'new public invariant type' in report
    print(json.dumps({
        'status': 'PASS', 'live': args.live, 'source_only': True,
        'local_pins': len(manifest['files']), 'root_pins': len(pins),
        'reviewed_ranges': sum(len(pin['reviewed_ranges']) for pin in pins),
        'new_lean_commands': 0, 'new_lake_commands': 0,
        'new_canonical_commands': 0, 'owned_public_pairs': 0,
        'constructed_pairs': 0, 'reused_proof_commands': 0,
        'proposed_heads_checked': False,
        'normality_already_proved': True,
        'prefix_resources_already_proved': True,
        'manifest_sha256': sha((here / 'audit-manifest.json').read_bytes()),
    }, indent=2))


if __name__ == '__main__':
    main()
