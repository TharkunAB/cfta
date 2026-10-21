#!/usr/bin/env python3
"""Verify independent dispatch review evidence without running Lean."""
from __future__ import annotations
import argparse
import datetime
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

HEAD = 'MicroCFTA.SourceCurrentResourceOwnerDispatch.key_ne_top'
PREFIX = 'resource-owner-dispatch-'
SOURCE_SHA = '1e287d68471babbaf486eee9e224ce5ed5cd3e9f30544053fd82da0e4c71ad7b'


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def relative(value: str) -> Path:
    path = Path(value)
    assert not path.is_absolute() and '..' not in path.parts
    return path


def check(path: Path, pin: dict) -> None:
    assert path.is_file() and path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256'], str(path)


def instant(value: str) -> datetime.datetime:
    return datetime.datetime.fromisoformat(value.replace('Z', '+00:00'))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = read(here / 'review-manifest.json')
    assert manifest['finalized']
    for pin in manifest['files']:
        check(here / relative(pin['path']), pin)
    pins = read(here / 'review-source-pins.json')['files']
    assert pins == manifest['sources']
    for pin in pins:
        snapshot = here / relative(pin['snapshot'])
        check(snapshot, pin)
        lines = snapshot.read_bytes().splitlines(keepends=True)
        if 'lines' in pin:
            assert len(lines) == pin['lines']
        for span in pin['reviewed_ranges']:
            lo, hi = span['start'], span['end']
            assert 1 <= lo <= hi <= len(lines)
            assert hashlib.sha256(b''.join(lines[lo - 1:hi])).hexdigest() == span['sha256']
        if args.live:
            check(args.root / relative(pin['path']), pin)
    selected = read(here / 'review-selection.json')
    assert selected['finalized'] and selected['public_heads'] == [HEAD]
    assert selected['reviewer_lean_jobs'] == selected['reviewer_canonical_jobs'] == selected['reviewer_public_pairs'] == selected['reviewer_official_edits'] == 0
    assert selected['copied_actual_author_lean_jobs'] == 3 and selected['copied_failed_checks'] == 1
    assert selected['copied_warning_checks'] == selected['copied_infrastructure_attempts'] == selected['copied_canonical_jobs'] == selected['copied_constructed_pairs'] == 0
    assert selected['complete_source_and_delta_reviewed'] and selected['public_header_byte_exact'] and selected['authorship_disclosed'] and selected['no_material_issues']
    owner = here / 'owner'
    assert sha(owner / (PREFIX + 'manifest.json')) == selected['owner_manifest_sha256'] == 'c3aaf13ce78ed3fea09e6e6647f785c632ae2ed13e70f170517a6291ed795e64'
    assert sha(owner / (PREFIX + 'selection.json')) == selected['owner_selection_sha256'] == 'f0992100a0717e8d98e596be78dd7c0fdaa78ebc529c8b46165ddd89c422936f'
    owner_command = [sys.executable, str(owner / (PREFIX + 'verify.py')), '--root', str(args.root)]
    if args.live:
        owner_command.append('--live')
    verified = subprocess.run(owner_command, cwd='/', check=True, capture_output=True, text=True)
    owner_result = json.loads(verified.stdout)
    assert owner_result['status'] == 'PASS' and owner_result['live'] == args.live
    text = (here / relative(selected['subject_source'])).read_text()
    assert hashlib.sha256(text.encode()).hexdigest() == selected['subject_source_sha256'] == SOURCE_SHA
    assert len(text.splitlines()) == selected['subject_lines'] == 187
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['key_ne_top']
    proposal = (owner / 'inputs/plan/proposed-signature.lean.txt').read_text()
    header = text.split('theorem key_ne_top\n', 1)[1].split(' := by', 1)[0]
    assert header == proposal.split('theorem key_ne_top\n', 1)[1].split('\nend MicroCFTA.', 1)[0]
    failed = (owner / (PREFIX + 'direct-1.source.lean')).read_text()
    assert text == failed.replace('(.node ownerEntry ownerRows ownerDepth ownerFree).referenceOf :=', '(.node ownerEntry ownerRows ownerDepth ownerFree : Node).referenceOf :=')
    assert (here / 'prelaunch-187.source.lean').read_text() == failed
    assert (here / 'reviewed-direct-1-repair.source.lean').read_text() == text
    assert text.count('SourceCurrentResourceParentWriters.edge_call formulas solver') == 1
    assert text.count('SourceCurrentResourceOwnerProgress.key_ne_top formulas solver') == 1
    assert 'SourceCurrentOuterOwnerSelection.selected' not in text
    expected = {PREFIX + 'direct-1': 1, PREFIX + 'direct-2': 0, PREFIX + 'public-1': 0}
    attempts = read(owner / (PREFIX + 'attempt-ledger.json'))['attempts']
    assert len(attempts) == 3 and {item['name']: item['exit_code'] for item in attempts} == expected
    for item in attempts:
        stem = item['name']
        receipt = read(owner / (stem + '.json'))
        assert receipt['exit_code'] == item['exit_code']
        assert sha(owner / receipt['source']) == receipt['sha256']
        assert read(owner / (stem + '.limits.json')) == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = read(owner / (stem + '.usage.json'))
        assert 0 <= usage['age_seconds'] <= 600 and usage['remaining_percent'] == 48
        start, end = instant(receipt['started_at']), instant(receipt['observed_at'])
        assert 0 <= (start - instant(usage['observed_at'])).total_seconds() <= 600
        assert 0 <= (end - start).total_seconds() < 300
    strict, public = selected['selected_strict'], selected['selected_public']
    assert (owner / (strict + '.log')).read_bytes() == b''
    assert (owner / (strict + '.source.lean')).read_text() == text
    full = owner / (public + '.log')
    assert full.stat().st_size == selected['readback_log_bytes'] == 9274578
    assert sha(full) == selected['readback_log_sha256'] == '3290e0161977d35675aa03a2796b3a4bf8257ef3979eadceb7fc03eb3de6daec'
    log = full.read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    checked, printed = log.split('@' + HEAD + ' :', 1)[1].split('\ntheorem ' + HEAD + ' :', 1)
    delimiters = list(re.finditer(r' :=\n(?=fun\b)', printed))
    assert len(delimiters) == 1
    boundary = delimiters[0]
    declared, proof = printed[:boundary.start()], printed[boundary.end():]
    assert ''.join(checked.split()) == ''.join(declared.split())
    assert len(''.join(checked.split())) == 23916 and '_private' not in checked + declared
    ax = re.search(re.escape("'" + HEAD + "' depends on axioms:") + r'\s*\[([^\]]*)\]', proof)
    assert ax and len(proof[:ax.start()]) > 1000
    names = sorted(name.strip() for name in re.sub(r'\.\{[^}]*\}', '', ax.group(1)).split(','))
    assert names == selected['axioms_by_head'][HEAD] == ['Classical.choice', 'Quot.sound', 'propext']
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']), 'root_pins': len(pins), 'reviewer_proof_jobs': 0, 'reviewer_canonical_jobs': 0, 'copied_actual_author_jobs': 3, 'copied_failed_checks': 1, 'copied_warning_checks': 0, 'public_heads': [HEAD], 'public_type_identity': True, 'owner_verifier': 'PASS', 'authorship_disclosed': True, 'manifest_sha256': sha(here / 'review-manifest.json')}, indent=2))


if __name__ == '__main__':
    main()
