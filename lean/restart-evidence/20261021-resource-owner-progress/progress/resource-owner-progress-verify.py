#!/usr/bin/env python3
"""Verify the exact owner progress proof evidence without running Lean."""
from __future__ import annotations
import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

PREFIX = 'resource-owner-progress-'
HEAD = 'MicroCFTA.SourceCurrentResourceOwnerProgress.key_ne_top'
SOURCE_SHA = '05b2dd2001743235a81a5190060e28bd61fdd1a044ecb2476096de85e2c11a0e'


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
    manifest = read(here / (PREFIX + 'manifest.json'))
    assert manifest['finalized']
    for pin in manifest['files']:
        check(here / relative(pin['path']), pin)
    pins = read(here / (PREFIX + 'source-pins.json'))['files']
    assert pins == manifest['sources']
    for pin in pins:
        snapshot = here / relative(pin['snapshot'])
        check(snapshot, pin)
        lines = snapshot.read_bytes().splitlines(keepends=True)
        assert len(lines) == pin['lines']
        for span in pin['reviewed_ranges']:
            assert 1 <= span['start'] <= span['end'] <= len(lines)
            assert hashlib.sha256(b''.join(lines[span['start'] - 1:span['end']])).hexdigest() == span['sha256']
        if args.live:
            check(args.root / relative(pin['path']), pin)
    selected = read(here / (PREFIX + 'selection.json'))
    assert selected['finalized'] and selected['public_heads'] == [HEAD]
    assert selected['new_public_pairs'] == 1
    assert selected['canonical_jobs'] == selected['constructed_pairs'] == selected['infrastructure_attempts'] == selected['prelaunch_proof_commands'] == 0
    assert not selected['official_edits_by_package_authors']
    source = here / relative(selected['source'])
    text = source.read_text()
    assert sha(source) == SOURCE_SHA == selected['source_sha256']
    assert len(text.splitlines()) == selected['source_lines'] == 117
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['key_ne_top']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b', text)
    original = (here / 'inputs/audit/proposed-signature.lean.txt').read_text()
    corrected = (here / 'corrected-proposal-qualified.lean.txt').read_text()
    needle = '(written : Written (bits := bits) formulas solver request returned)'
    replacement = '(written : SourceCurrentResourceParentWriters.Written (bits := bits) formulas solver request returned)'
    assert original.count(needle) == 1 and corrected == original.replace(needle, replacement)
    assert sha(here / 'corrected-proposal-qualified.lean.txt') == selected['corrected_proposal_sha256']
    assert sha(here / 'inputs/audit/proposed-signature.lean.txt') == selected['original_proposal_sha256']
    actual_header = text.split('theorem key_ne_top\n', 1)[1].split(' := by', 1)[0]
    proposed_header = corrected.split('theorem key_ne_top\n', 1)[1].split('\nend MicroCFTA.', 1)[0]
    assert actual_header == proposed_header and selected['public_header_byte_exact_corrected_proposal']
    assert not selected['original_proposal_elaborated']
    failed1 = (here / (PREFIX + 'direct-1.source.lean')).read_text()
    failed2 = (here / (PREFIX + 'direct-2.source.lean')).read_text()
    assert failed2 == failed1.replace(needle, replacement)
    expected = failed2.replace(
        '  obtain ⟨loaded,middle,records,kept,scanned,scanFourth,preparedValues,preparedHeap,',
        '  have nativeGood := SourceCurrentNativeOperationHeap.Good.of_native\n    (SourceCurrentNativeOperationInvariants.Good.of_checked context.ready.good) context.ready.semantic context.ready.costs\n  obtain ⟨loaded,middle,records,kept,scanned,scanFourth,preparedValues,preparedHeap,').replace(
        'SourceCurrentActualOwnerSelection.selected observed context.ready.good',
        'SourceCurrentActualOwnerSelection.selected observed nativeGood').replace(
        '          simpa only [keep,ite_true,readback] using constructed.guard',
        '          have acceptedGuard : returned.entry.key.constraint = SourceEqualityConjoinAllocation.readback loaded := by\n            simpa only [keep,ite_true] using constructed.guard\n          exact acceptedGuard.trans readback')
    assert text == expected
    ledger = read(here / (PREFIX + 'attempt-ledger.json'))
    attempts = ledger['attempts']
    expected_attempts = {PREFIX + 'direct-1': (1, 'required_memos'), PREFIX + 'direct-2': (1, 'required_memos'), PREFIX + 'direct-3': (0, 'guard_inventory'), PREFIX + 'public-1': (0, 'guard_inventory')}
    assert len(attempts) == len({item['name'] for item in attempts}) == selected['lean_jobs'] == 4
    assert {item['name']: (item['exit_code'], item['owner']) for item in attempts} == expected_attempts
    receipt_names = {path.stem for path in here.glob(PREFIX + '*.json') if re.fullmatch(PREFIX + r'(?:direct|public)-\d+', path.stem)}
    assert receipt_names == set(expected_attempts)
    failed_count = warning_count = 0
    for item in attempts:
        stem = item['name']
        receipt = read(here / (stem + '.json'))
        raw_path = here / (stem + '.log')
        assert item['kind'] == 'lean' and item['lean_launched']
        assert receipt['exit_code'] == item['exit_code']
        assert sha(here / (stem + '.json')) == item['receipt_sha256'] and sha(raw_path) == item['log_sha256']
        assert sha(here / relative(receipt['source'])) == receipt['sha256'] == item['source_sha256']
        assert receipt['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert receipt['command'][1] == '-Dlinter.all=true'
        assert receipt['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
        assert read(here / relative(receipt['limits'])) == {'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = read(here / (stem + '.usage.json'))
        assert 0 <= usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
        start, end = instant(receipt['started_at']), instant(receipt['observed_at'])
        assert 0 <= (start - instant(usage['observed_at'])).total_seconds() <= 600
        assert 0 <= (end - start).total_seconds() < 300
        warnings = len(re.findall(r'\bwarning(?:\([^)]*\))?:', raw_path.read_text()))
        assert warnings == item['warning_diagnostics']
        warning_count += warnings > 0
        failed_count += receipt['exit_code'] != 0
    assert failed_count == selected['failed_checks'] == 2 and warning_count == selected['warning_checks'] == 0
    assert ledger['ownership'] == selected['ownership'] == {'required_memos': 2, 'guard_inventory': 2}
    strict, public = selected['selected_strict'], selected['selected_public']
    assert read(here / (strict + '.json'))['exit_code'] == read(here / (public + '.json'))['exit_code'] == 0
    assert (here / (strict + '.log')).read_bytes() == b''
    assert (here / (strict + '.source.lean')).read_bytes() == source.read_bytes()
    printer = (here / (public + '.source.lean')).read_text()
    assert printer == (here / (PREFIX + 'public.lean')).read_text() and printer.startswith(text + '\n')
    for option in ['linter.all true', 'pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254', 'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000']:
        assert printer.count('set_option ' + option) == 1
    for directive in ['#check @', '#print ', '#print axioms ']:
        assert printer.count(directive + HEAD) == 1
    raw = here / (public + '.log')
    assert raw.stat().st_size == selected['public_log_bytes'] == 10187067
    assert sha(raw) == selected['public_log_sha256']
    log = raw.read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    checked, printed = log.split('@' + HEAD + ' :', 1)[1].split('\ntheorem ' + HEAD + ' :', 1)
    delimiters = list(re.finditer(r' :=\n(?=fun\b)', printed))
    assert len(delimiters) == 1
    boundary = delimiters[0]
    declared, proof = printed[:boundary.start()], printed[boundary.end():]
    assert ''.join(checked.split()) == ''.join(declared.split())
    assert '_private' not in checked + declared
    ax = re.search(re.escape("'" + HEAD + "' depends on axioms:") + r'\s*\[([^\]]*)\]', proof)
    assert ax and len(proof[:ax.start()]) > 1000
    names = sorted(name.strip() for name in re.sub(r'\.\{[^}]*\}', '', ax.group(1)).split(','))
    assert names == selected['axioms_by_head'][HEAD] == ['Classical.choice', 'Quot.sound', 'propext']
    correction = read(here / 'full-type-parser-correction.json')
    assert correction['lean_exit_code'] == 0 and correction['additional_lean_jobs'] == 0 and not correction['source_changed']
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']), 'root_pins': len(pins), 'actual_lean_commands': 4, 'failed_checks': 2, 'warning_checks': 0, 'ownership': selected['ownership'], 'canonical_jobs': 0, 'infrastructure_attempts': 0, 'constructed_pairs': 0, 'public_heads': [HEAD], 'public_type_identity': True, 'axioms_by_head': selected['axioms_by_head'], 'manifest_sha256': sha(here / (PREFIX + 'manifest.json'))}, indent=2))


if __name__ == '__main__':
    main()
