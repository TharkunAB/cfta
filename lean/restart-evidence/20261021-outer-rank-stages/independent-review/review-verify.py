#!/usr/bin/env python3
"""Verify frozen independent source and public readback evidence."""
from __future__ import annotations
import argparse
import datetime
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path


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
    parser.add_argument('--toolchain-source', type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = read(here / 'review-manifest.json')
    assert manifest['finalized']
    for pin in manifest['files']:
        check(here / relative(pin['path']), pin)
    pins = read(here / 'review-source-pins.json')['sources']
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
    evidence = read(here / 'review-source-pins.json')
    toolchain_pins = evidence['toolchain_sources']
    assert toolchain_pins == manifest['toolchain_sources']
    toolchain = args.toolchain_source or Path(evidence['toolchain_source_root'])
    for pin in toolchain_pins:
        snapshot = here / relative(pin['snapshot'])
        check(snapshot, pin)
        lines = snapshot.read_bytes().splitlines(keepends=True)
        assert len(lines) == pin['lines']
        for span in pin['reviewed_ranges']:
            lo, hi = span['start'], span['end']
            assert 1 <= lo <= hi <= len(lines)
            assert hashlib.sha256(b''.join(lines[lo - 1:hi])).hexdigest() == span['sha256']
        if args.live:
            check(toolchain / relative(pin['path']), pin)
    selected = read(here / 'review-selection.json')
    assert selected['finalized'] and selected['complete_source_and_deltas_reviewed']
    assert selected['authorship_disclosed'] and selected['material_issues'] == []
    assert selected['reviewer_proof_jobs'] == selected['reviewer_runtime_jobs'] == selected['reviewer_official_edits'] == 0
    owner, prefix = here / 'owner', selected['owner_prefix']
    assert sha(owner / (prefix + 'manifest.json')) == selected['owner_manifest_sha256']
    assert sha(owner / (prefix + 'selection.json')) == selected['owner_selection_sha256']
    command = [sys.executable, str(owner / (prefix + 'verify.py')), '--root', str(args.root)]
    if args.live:
        command.append('--live')
        command += ['--toolchain-source', str(toolchain)]
    result = subprocess.run(command, cwd='/', capture_output=True, text=True, check=True)
    owner_result = json.loads(result.stdout)
    assert owner_result['status'] == 'PASS' and owner_result['live'] == args.live
    subject = owner / relative(selected['source'])
    source = subject.read_text()
    assert sha(subject) == selected['source_sha256']
    assert len(source.splitlines()) == selected['source_lines']
    heads = selected['public_heads']
    assert re.findall(r'^(?:theorem|(?:noncomputable )?def) (\w+)', source, re.M) == [head.rsplit('.', 1)[1] for head in heads]
    attempts = [path for path in owner.glob(prefix + '*.json') if re.fullmatch(prefix + r'(?:direct|public)-\d+', path.stem)]
    assert len(attempts) == selected['copied_actual_author_jobs']
    failures = warnings = 0
    for path in attempts:
        receipt = read(path)
        failures += receipt['exit_code'] != 0
        raw = (owner / (path.stem + '.log')).read_text()
        warnings += bool(re.search(r'\bwarning(?:\([^)]*\))?:', raw))
        assert sha(owner / relative(receipt['source'])) == receipt['sha256']
        assert read(owner / (path.stem + '.limits.json')) == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = read(owner / (path.stem + '.usage.json'))
        assert 0 <= usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
        start, end = instant(receipt['started_at']), instant(receipt['observed_at'])
        assert 0 <= (start - instant(usage['observed_at'])).total_seconds() <= 600
        assert 0 <= (end - start).total_seconds() < 300
    assert failures == selected['copied_failed_checks'] and warnings == selected['copied_warning_checks']
    strict, public = selected['selected_strict'], selected['selected_public']
    assert read(owner / (strict + '.json'))['exit_code'] == read(owner / (public + '.json'))['exit_code'] == 0
    assert (owner / (strict + '.log')).read_bytes() == b''
    assert (owner / (strict + '.source.lean')).read_text() == source
    printer = (owner / (public + '.source.lean')).read_text()
    assert printer.startswith(source + '\n')
    for setting in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert printer.count('set_option ' + setting) == 1
    full = owner / (public + '.log')
    assert full.stat().st_size == selected['public_log_bytes'] and sha(full) == selected['public_log_sha256']
    log = full.read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    actual_axioms = {}
    for index, head in enumerate(heads):
        markers = list(re.finditer(r'^@?' + re.escape(head) + r'\s*:', log, re.M))
        assert len(markers) == 1
        end = len(log) if index + 1 == len(heads) else re.search(r'^@?' + re.escape(heads[index + 1]) + r'\s*:', log, re.M).start()
        kind = selected['public_kinds'][head]
        checked, printed = log[markers[0].end():end].split('\n' + kind + ' ' + head + ' :', 1)
        boundaries = [match for match in re.finditer(r' :=\n', printed)
            if ''.join(printed[:match.start()].split()) == ''.join(checked.split())]
        assert len(boundaries) == 1
        boundary = boundaries[0]
        declared, proof = printed[:boundary.start()], printed[boundary.end():]
        assert ''.join(checked.split()) == ''.join(declared.split()) and '_private' not in checked + declared
        ax = re.search(re.escape("'" + head + "'") + r' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)', proof)
        assert ax and proof.startswith('fun ') and len(proof[:ax.start()]) > 50
        names = sorted(name.strip() for name in re.sub(r'\.\{[^}]*\}', '', ax.group(1) or '').split(',') if name.strip())
        assert names == selected['axioms_by_head'][head]
        assert set(names) <= {'Classical.choice', 'Quot.sound', 'propext'}
        actual_axioms[head] = names
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']), 'root_pins': len(pins), 'root_reviewed_ranges': sum(len(pin['reviewed_ranges']) for pin in pins), 'toolchain_pins': len(toolchain_pins), 'toolchain_reviewed_ranges': sum(len(pin['reviewed_ranges']) for pin in toolchain_pins), 'reviewer_proof_jobs': 0, 'reviewer_native_runtime_jobs': 0, 'reviewer_official_edits': 0, 'copied_actual_author_jobs': len(attempts), 'copied_failed_checks': failures, 'copied_warning_checks': warnings, 'public_heads': heads, 'whole_public_type_identity': True, 'owner_verifier': 'PASS', 'axioms_by_head': actual_axioms, 'manifest_sha256': sha(here / 'review-manifest.json')}, indent=2))


if __name__ == '__main__':
    main()
