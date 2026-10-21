#!/usr/bin/env python3
"""Verify the source-only independent completion audit."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def relative(name):
    path = Path(name)
    assert not path.is_absolute() and '..' not in path.parts
    return path

def check(path, pin):
    assert path.is_file() and path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256'], str(path)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    read = lambda name: json.loads((here / name).read_text())
    manifest, selected = read('review-manifest.json'), read('review-selection.json')
    assert manifest['finalized'] and selected['finalized'] and selected['authorship_disclosed']
    assert selected['material_issues'] == [] and selected['new_completion_head'] is None
    for name in ['reviewer_proof_jobs', 'reviewer_runtime_jobs', 'reviewer_official_edits', 'copied_owner_proof_jobs']:
        assert selected[name] == 0
    for pin in manifest['files']:
        check(here / relative(pin['path']), pin)
    pins = read('review-source-pins.json')['sources']
    assert pins == manifest['sources'] and len(pins) == selected['whole_sources_pinned'] == 21
    assert sum(len(p['reviewed_ranges']) for p in pins) == selected['source_ranges'] == 28
    for pin in pins:
        snapshot = here / relative(pin['snapshot'])
        check(snapshot, pin)
        lines = snapshot.read_bytes().splitlines(keepends=True)
        for span in pin['reviewed_ranges']:
            lo, hi = span['start'], span['end']
            assert 1 <= lo <= hi <= len(lines)
            assert hashlib.sha256(b''.join(lines[lo - 1:hi])).hexdigest() == span['sha256']
        if args.live:
            check(args.root / relative(pin['path']), pin)
    assert sha(here / 'owner/manifest.json') == selected['owner_manifest_sha256']
    assert sha(here / 'reviewed-plan.md') == selected['reviewed_plan_sha256']
    command = [sys.executable, str(here / 'owner/verify.py'), '--root', str(args.root)]
    if args.live:
        command.append('--live')
    owner = json.loads(subprocess.check_output(command, cwd='/'))
    assert owner['status'] == 'PASS' and owner['live'] == args.live
    for name in ['lean_jobs', 'lake_jobs', 'canonical_jobs', 'runtime_jobs', 'public_pairs']:
        assert owner[name] == 0
    assert owner['completion_proved'] is False and owner['proposed_public_head'] is None
    print(json.dumps(dict(status='PASS', live=args.live, local_pins=len(manifest['files']), root_pins=len(pins), source_ranges=28, reviewer_proof_jobs=0, reviewer_runtime_jobs=0, reviewer_official_edits=0, copied_owner_proof_jobs=0, completion_proved=False, proposed_public_head=None, owner_verifier='PASS', manifest_sha256=sha(here / 'review-manifest.json')), indent=2))

if __name__ == '__main__':
    main()
