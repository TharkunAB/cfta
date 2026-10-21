#!/usr/bin/env python3
"""Verify the local resource writer proof and every retained Lean attempt."""
from __future__ import annotations
import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

PREFIX = 'resource-writers-'
NAMESPACE = 'MicroCFTA.SourceCurrentResourceParentWriters.'
HEADS = [NAMESPACE + name for name in ('Written', 'Origins', 'initial', 'edge_call')]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def relative(value: str) -> Path:
    path = Path(value)
    assert not path.is_absolute() and '..' not in path.parts, value
    return path


def check(path: Path, pin: dict) -> None:
    assert path.is_file() and path.stat().st_size == pin['bytes'] and sha(path) == pin['sha256'], str(path)


def instant(value: str) -> datetime.datetime:
    return datetime.datetime.fromisoformat(value.replace('Z', '+00:00'))


def public_piece(text: str, kind: str, name: str) -> str:
    tail = text[text.index(kind + ' ' + name):].split('\n\n', 1)[0]
    if kind == 'theorem':
        tail = re.split(r'\s+:=(?: by)?\n', tail, maxsplit=1)[0]
    return re.sub(r'\s+', '', tail)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
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
        for span in pin['reviewed_ranges']:
            lo, hi = span['start'], span['end']
            assert 1 <= lo <= hi <= len(lines)
            assert hashlib.sha256(b''.join(lines[lo-1:hi])).hexdigest() == span['sha256']
        if args.live:
            check(args.root / relative(pin['path']), pin)
    selected = read(here / (PREFIX + 'selection.json'))
    assert selected['finalized'] and selected['public_heads'] == HEADS
    assert selected['canonical_jobs'] == selected['constructed_pairs'] == selected['infrastructure_attempts'] == 0
    assert selected['new_public_pairs'] == 4 and not selected['official_edits']
    assert selected['groups'] == [{'name': 'resource-parent-writers', 'pairs': 4, 'full_proof': True, 'kind': 'production'}]
    source = here / relative(selected['source'])
    text = source.read_text()
    assert sha(source) == selected['source_sha256'] and len(text.splitlines()) == selected['source_lines'] == 250
    assert re.findall(r'^def (\w+)', text, re.M) == ['Written', 'Origins']
    assert re.findall(r'^theorem (\w+)', text, re.M) == ['initial', 'edge_call']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b', text)
    proposed = (here / 'inputs/plan/proposed-signatures.lean.txt').read_text()
    for kind, name in [('def', 'Written'), ('def', 'Origins'), ('theorem', 'initial'), ('theorem', 'edge_call')]:
        assert public_piece(text, kind, name) == public_piece(proposed, kind, name), name
    assert sha(here / 'resource-writers-source-only.lean') == 'af6daa811aedb1d321c00fdcaa4a2c2f93cc86f2ef6d95cf3287334191518319'
    assert (here / 'resource-writers-source-only.lean').read_bytes() == (here / 'resource-writers-prelaunch-250.lean').read_bytes()
    assert sha(here / 'resource-writers-direct-1.source.lean') == '119d15cb87a72f8a3d5946e55e8f1cc5ad99c2d8f59a439cb5bd31061a79027c'
    written = text.split('def Written ', 1)[1].split('\n\n', 1)[0]
    assert written.count('  ∃ ') == 1 and 'SupportedWritten' not in written
    for clause in ('writerBefore : Caller (bits + 2)', 'Context formulas solver inventory writerBefore globals',
                   'Frame formulas solver inventory writerBefore.checked', 'Fits profile writerBefore.checked',
                   'residentReserved bits budget request writerBefore.checked profile',
                   'NativeSupport writerBefore.checked.native.machine.heap writerBefore.checked.native',
                   'Nonempty (History empty writerBefore.checked.native.machine.heap)',
                   'MergeStored writerBefore.merge', 'MergePositive writerBefore.merge'):
        assert clause in written, clause
    for law in ('FlatMemoThunk.CellSpec', 'FlatMemoThunk.demand_spec', 'FlatMemoThunk.finish_spec',
                'FlatMemoThunk.demand_ready_original', 'ready_eq_of_identity', 'edge_identity_unique',
                'SourceCurrentAllocatedPartialCallSteps.edge_start'):
        assert law in text, law
    assert 'theorem reached' not in text and 'omit [' not in text
    assert text.index('private theorem request_eq') < text.index('variable [DecidableEq Symbol]')
    ledger = read(here / (PREFIX + 'attempt-ledger.json'))['attempts']
    assert len(ledger) == sum(item['lean_launched'] for item in ledger) == selected['lean_jobs'] == 3
    assert {item['name']: item['exit_code'] for item in ledger} == selected['attempts']
    assert sum(item['exit_code'] != 0 for item in ledger) == selected['failed_checks'] == 1
    receipts = {path.stem for path in here.glob('resource-writers-*.json')
                if re.fullmatch(r'resource-writers-(?:direct|public)-\d+', path.stem)}
    assert receipts == {item['name'] for item in ledger}
    warning_jobs = 0
    for item in ledger:
        stem = item['name']
        receipt = read(here / (stem + '.json'))
        log_path = here / (stem + '.log')
        assert sha(here / (stem + '.json')) == item['receipt_sha256'] and sha(log_path) == item['log_sha256']
        assert item['kind'] == 'lean' and item['lean_launched'] and receipt['exit_code'] == item['exit_code']
        assert sha(here / relative(receipt['source'])) == receipt['sha256']
        assert receipt['command'][0] == '/home/tritlo/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean'
        assert receipt['command'][1] == '-Dlinter.all=true'
        assert receipt['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
        assert read(here / relative(receipt['limits'])) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = read(here / (stem + '.usage.json'))
        assert usage['age_seconds'] <= 600 and usage['remaining_percent'] > 1
        start, end = instant(receipt['started_at']), instant(receipt['observed_at'])
        assert 0 <= (start-instant(usage['observed_at'])).total_seconds() <= 600
        assert 0 <= (end-start).total_seconds() < 300
        warning_jobs += int(bool(re.search(r'\bwarning(?:\([^)]*\))?:', log_path.read_text())))
    assert selected['warning_checks'] == warning_jobs == 0
    strict = selected['selected_strict']
    assert read(here / (strict + '.json'))['exit_code'] == 0
    assert (here / (strict + '.log')).read_bytes() == b''
    assert (here / (strict + '.source.lean')).read_bytes() == source.read_bytes()
    stem = selected['selected_public']
    assert read(here / (stem + '.json'))['exit_code'] == 0
    printer = (here / (stem + '.source.lean')).read_text()
    assert printer == (here / (PREFIX + 'public.lean')).read_text() and printer.startswith(text)
    for option in ('pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254',
                   'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'linter.all true'):
        assert printer.count('set_option ' + option) == 1
    log_path = here / (stem + '.log')
    assert log_path.stat().st_size == selected['public_log_bytes'] and sha(log_path) == selected['public_log_sha256']
    log = log_path.read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    axiom_sets = {}
    for head, kind in zip(HEADS, ('def', 'def', 'theorem', 'theorem')):
        for directive in ('#check @', '#print ', '#print axioms '):
            assert printer.count(directive + head) == 1
        checked, printed = log.split('@' + head + ' :', 1)[1].split('\n' + kind + ' ' + head + ' :', 1)
        declared, proof = printed.split(' :=', 1)
        assert ''.join(checked.split()) == ''.join(declared.split()), head
        assert '_private' not in checked + declared, head
        report = re.search(re.escape("'" + head + "' depends on axioms:") + r'\s*\[([^\]]*)\]', proof)
        assert report and len(proof[:report.start()]) > 500, head
        actual = {part.strip() for part in re.sub(r'\.\{[^}]*\}', '', report.group(1)).split(',')}
        assert actual == {'propext', 'Classical.choice', 'Quot.sound'}
        axiom_sets[head] = sorted(actual)
    assert axiom_sets == selected['axioms_by_head']
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
                      'root_pins': len(pins), 'lean_jobs': 3, 'failed_checks': 1, 'warning_checks': 0,
                      'infrastructure_attempts': 0, 'canonical_jobs': 0, 'public_pairs': 4,
                      'constructed_pairs': 0, 'public_type_identity': True, 'axioms_by_head': axiom_sets,
                      'manifest_sha256': sha(here / (PREFIX + 'manifest.json'))}, indent=2))


if __name__ == '__main__':
    main()
