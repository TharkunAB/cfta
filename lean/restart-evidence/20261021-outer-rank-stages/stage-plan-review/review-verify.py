#!/usr/bin/env python3
"""Check the frozen source review. Do not run a proof or the envelope."""
from __future__ import annotations
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def relative(name: str) -> Path:
    path = Path(name)
    assert not path.is_absolute() and '..' not in path.parts
    return path


def check(path: Path, pin: dict) -> None:
    assert path.is_file() and path.stat().st_size == pin['bytes']
    assert sha(path) == pin['sha256'], str(path)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--toolchain-source', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = read(here / 'review-manifest.json')
    assert manifest['finalized'] and manifest['source_only']
    for pin in manifest['files']:
        check(here / relative(pin['path']), pin)
    evidence = read(here / 'review-source-pins.json')
    for key, origin in [('sources', args.root), ('toolchain_sources', args.toolchain_source)]:
        assert evidence[key] == manifest[key]
        for pin in evidence[key]:
            snapshot = here / relative(pin['snapshot'])
            check(snapshot, pin)
            lines = snapshot.read_bytes().splitlines(keepends=True)
            assert len(lines) == pin['lines']
            for span in pin['reviewed_ranges']:
                lo, hi = span['start'], span['end']
                assert 1 <= lo <= hi <= len(lines)
                assert hashlib.sha256(b''.join(lines[lo - 1:hi])).hexdigest() == span['sha256']
            if args.live:
                check(origin / relative(pin['path']), pin)
    selected = read(here / 'review-owner-selection.json')
    assert selected['owner_frozen'] and selected['source_only']
    assert selected['selected_public_heads'] == ['stage_bounds']
    assert selected['hard_total_source_line_stop'] == 250
    assert not selected['stage_bounds_proved'] and not selected['physical_adequacy_proved']
    assert not selected['implementation_authorized']
    assert selected['reviewer_proof_jobs'] == selected['reviewer_runtime_jobs'] == selected['reviewer_official_edits'] == 0
    owner = here / 'owner'
    assert sha(owner / 'manifest.json') == selected['owner_manifest_sha256']
    assert sha(owner / 'selection.json') == selected['owner_selection_sha256']
    proposed = (owner / 'proposed-signature.lean.txt').read_bytes()
    original = (owner / 'historical/original-42-line-proposal.lean.txt').read_bytes()
    assert len(proposed.splitlines()) == 34 and proposed == b''.join(original.splitlines(keepends=True)[8:])
    assert hashlib.sha256(proposed).hexdigest() == '473b65048b665c273877a1a38f73dce6f2f63001abcd7a40ce79ad86b534293e'
    command = [sys.executable, str(owner / 'verify.py'), '--root', str(args.root), '--toolchain-source', str(args.toolchain_source)]
    if args.live:
        command.append('--live')
    result = subprocess.run(command, cwd='/', check=True, capture_output=True, text=True)
    actual = json.loads(result.stdout)
    assert actual['status'] == 'PASS' and actual['live'] == args.live
    assert actual['root_pins'] == actual['toolchain_pins'] == 5 and actual['source_ranges'] == 22
    assert actual['proof_jobs'] == actual['runtime_jobs'] == actual['canonical_jobs'] == 0
    assert read(here / 'clearance.json')['judgment'] == 'clear'
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
        'root_pins': len(evidence['sources']),
        'root_reviewed_ranges': sum(len(x['reviewed_ranges']) for x in evidence['sources']),
        'toolchain_pins': len(evidence['toolchain_sources']),
        'toolchain_reviewed_ranges': sum(len(x['reviewed_ranges']) for x in evidence['toolchain_sources']),
        'owner_index_sources': 10, 'owner_index_ranges': 22, 'owner_verifier': 'PASS',
        'reviewer_proof_jobs': 0, 'reviewer_runtime_jobs': 0, 'reviewer_official_edits': 0,
        'stage_bounds_proved': False, 'physical_adequacy_proved': False,
        'implementation_authorized': False, 'manifest_sha256': sha(here / 'review-manifest.json')}, indent=2))


if __name__ == '__main__':
    main()
