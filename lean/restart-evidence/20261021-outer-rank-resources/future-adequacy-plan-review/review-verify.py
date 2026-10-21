#!/usr/bin/env python3
"""Verify the frozen source plan review and its current source files."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def relative(text: str) -> Path:
    path = Path(text)
    assert not path.is_absolute() and '..' not in path.parts
    return path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = read(here / 'review-manifest.json')
    selected = read(here / 'review-selection.json')
    assert manifest['finalized'] and selected['finalized']
    for pin in manifest['files']:
        path = here / relative(pin['path'])
        assert path.is_file() and path.stat().st_size == pin['bytes']
        assert digest(path) == pin['sha256'], str(path)
    assert selected['material_issues'] == []
    assert selected['whole_plan_header_context_report_and_all_ranges_reviewed']
    assert selected['authored_foundations_disclosed']
    assert selected['reviewer_proof_jobs'] == selected['reviewer_runtime_jobs'] == selected['reviewer_official_edits'] == 0
    assert not selected['implementation_authorized_by_review']
    assert selected['hard_total_source_stop'] == 650
    owner = here / 'owner'
    assert digest(owner / 'manifest.json') == selected['owner_manifest_sha256']
    assert digest(owner / 'selection.json') == selected['owner_selection_sha256']
    assert digest(owner / 'report.md') == selected['owner_report_sha256']
    assert digest(owner / 'proposed-signature.lean.txt') == selected['public_header_sha256']
    pins = read(here / 'review-source-pins.json')
    index = read(owner / 'source-index.json')
    assert pins['root_sources'] == index['sources']
    assert pins['snapshots'] == read(owner / 'snapshots.json')
    assert pins['root_count'] == len(index['sources']) == 24
    assert pins['range_count'] == sum(len(source['ranges']) for source in index['sources']) == 32
    assert pins['all_reviewed_ranges']
    command = [sys.executable, str(owner / 'verify.py'), '--root', str(args.root)]
    if args.live:
        command.append('--live')
    result = subprocess.run(command, cwd='/', capture_output=True, text=True, check=True)
    checked = json.loads(result.stdout)
    assert checked['status'] == 'PASS' and checked['live'] == args.live
    print(json.dumps({'status': 'PASS', 'live': args.live,
        'local_pins': len(manifest['files']), 'root_sources': 24, 'reviewed_ranges': 32,
        'reviewer_proof_jobs': 0, 'reviewer_runtime_jobs': 0, 'reviewer_official_edits': 0,
        'owner_verifier': 'PASS', 'public_headers': 1,
        'manifest_sha256': digest(here / 'review-manifest.json')}, indent=2))


if __name__ == '__main__':
    main()
