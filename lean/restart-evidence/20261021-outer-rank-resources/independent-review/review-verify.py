#!/usr/bin/env python3
"""Verify the frozen independent proof review without running Lean or C."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import re
import subprocess
import sys


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def relative(value: str) -> Path:
    path = Path(value)
    assert not path.is_absolute() and '..' not in path.parts
    return path


def instant(value: str) -> datetime.datetime:
    return datetime.datetime.fromisoformat(value.replace('Z', '+00:00'))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--toolchain-source', type=Path, required=True)
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
    assert selected['whole_source_and_all_deltas_reviewed']
    assert selected['whole_public_type_reviewed'] and selected['complete_body_reader_checked']
    assert not selected['entire_printed_body_manually_read']
    assert selected['authored_foundations_disclosed'] and selected['material_issues'] == []
    assert selected['reviewer_proof_jobs'] == selected['reviewer_runtime_jobs'] == selected['reviewer_official_edits'] == 0
    owner = here / 'owner'
    prefix = 'outer-rank-resources-'
    assert digest(owner / (prefix + 'manifest.json')) == selected['owner_manifest_sha256']
    assert digest(owner / (prefix + 'selection.json')) == selected['owner_selection_sha256']
    assert digest(owner / (prefix + 'report.md')) == selected['owner_report_sha256']
    pins = read(here / 'review-source-pins.json')
    assert pins['sources'] == read(owner / 'source-pins.json')['sources']
    assert pins['all_ranges_reviewed']
    assert sum(pin['authority'] == 'root' for pin in pins['sources']) == 19
    assert sum(pin['authority'] == 'toolchain' for pin in pins['sources']) == 1
    assert sum(len(pin['reviewed_ranges']) for pin in pins['sources']) == 40
    command = [sys.executable, str(owner / (prefix + 'verify.py')),
        '--root', str(args.root), '--toolchain-source', str(args.toolchain_source)]
    if args.live:
        command.append('--live')
    result = subprocess.run(command, cwd='/', capture_output=True, text=True, check=True)
    checked = json.loads(result.stdout)
    assert checked['status'] == 'PASS' and checked['live'] == args.live
    ledger = read(owner / 'attempt-ledger.json')
    assert ledger['actual_lean_jobs'] == 8 and ledger['failed_jobs'] == 6
    assert ledger['error_diagnostics'] == 43 and ledger['warning_diagnostics'] == 0
    for attempt in ledger['attempts']:
        receipt = read(owner / relative(attempt['receipt']))
        usage = read(owner / relative(attempt['usage']))
        start, end = instant(receipt['started_at']), instant(receipt['observed_at'])
        assert 0 <= (start - instant(usage['observed_at'])).total_seconds() <= 600
        assert 0 <= (end - start).total_seconds() < 300
    source = owner / 'SourceCurrentOuterRankEnvelopeResources.lean'
    assert digest(source) == selected['source_sha256']
    assert len(source.read_bytes().splitlines()) == selected['source_lines'] == 481
    readback = read(here / 'public-readback.json')
    assert readback == read(owner / (prefix + 'full-public-readback.json'))
    assert readback['log_bytes'] == 62309163
    assert readback['log_sha256'] == selected['public_log_sha256']
    head = readback['heads'][0]
    assert head['checked_type_characters'] == 32021 and head['normalized_type_characters'] == 18804
    assert head['body_characters'] == 62243672
    assert head['actual_axioms'] == ['Classical.choice', 'Quot.sound', 'propext']
    assert head['head'] == selected['public_head']
    assert selected['conditional_success_resources_only']
    assert not selected['adequacy_proved'] and not selected['capacity_resolved']
    assert digest(owner / (prefix + 'check-full-public.py')) == '31dd87fc9bf23f277ae89943e900fe8a978b66d8c8e87ba252acc7aec2f9517f'
    print(json.dumps({'status': 'PASS', 'live': args.live,
        'local_pins': len(manifest['files']), 'root_pins': 19, 'toolchain_pins': 1,
        'reviewed_ranges': 40, 'copied_author_jobs': 8, 'copied_failed_jobs': 6,
        'reviewer_proof_jobs': 0, 'reviewer_runtime_jobs': 0, 'reviewer_official_edits': 0,
        'owner_verifier': 'PASS', 'public_type_identity': True,
        'manifest_sha256': digest(here / 'review-manifest.json')}, indent=2))


if __name__ == '__main__':
    main()
