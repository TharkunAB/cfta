#!/usr/bin/env python3
"""Verify the completed checked-trace scope adapter without running Lean."""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

SHA = '924446496dd6d5fe0032bd703411d0dbdb5d5595e904d56516a2cb422e18f6da'
PREFIX = 'actual-scope-'
HEADS = ['MicroCFTA.SourceCurrentAllocatedNativeActualScope.word_ranges',
         'MicroCFTA.SourceCurrentAllocatedNativeActualScope.step']


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def check(path: Path, pin: dict) -> None:
    assert path.is_file() and path.stat().st_size == pin['bytes'], str(path)
    assert sha(path) == pin['sha256'], str(path)


def instant(value: str) -> datetime.datetime:
    return datetime.datetime.fromisoformat(value.replace('Z', '+00:00'))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = read(here / (PREFIX + 'manifest.json'))
    assert manifest['finalized']
    for pin in manifest['files']:
        path = Path(pin['path'])
        assert not path.is_absolute() and '..' not in path.parts
        check(here / path, pin)
    pins = read(here / (PREFIX + 'source-pins.json'))['files']
    assert manifest['sources'] == pins
    for pin in pins:
        check(here / 'inputs/root' / pin['path'], pin)
        if args.live:
            check(args.root / pin['path'], pin)
    selected = read(here / (PREFIX + 'selection.json'))
    assert selected['finalized'] and selected['source_sha256'] == SHA
    assert selected['public_heads'] == HEADS
    assert (selected['lean_jobs'], selected['failed_checks'], selected['warning_checks'],
            selected['canonical_jobs'], selected['infrastructure_attempts']) == (3, 1, 0, 0, 1)
    assert (selected['new_public_pairs'], selected['constructed_pairs']) == (2, 0)
    assert selected['selected_strict'] == PREFIX + 'direct-3'
    assert selected['selected_public'] == PREFIX + 'public-1'
    source = here / selected['source']
    assert sha(source) == SHA and len(source.read_text().splitlines()) == 78
    assert re.findall(r'^theorem (\w+)', source.read_text(), re.M) == ['word_ranges', 'step']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b', source.read_text())
    if args.live:
        assert sha(args.root / 'lean/MicroCFTA' / source.name) == SHA
    ledger = read(here / (PREFIX + 'attempt-ledger.json'))['attempts']
    assert len(ledger) == 4 and sum(item['lean_launched'] for item in ledger) == 3
    assert {item['name']: item['exit_code'] for item in ledger} == selected['attempts']
    for item in ledger:
        stem = item['name']
        receipt_path = here / (stem + '.json')
        log_path = here / (stem + '.log')
        assert sha(receipt_path) == item['receipt_sha256'] and sha(log_path) == item['log_sha256']
        receipt = read(receipt_path)
        assert receipt['exit_code'] == item['exit_code']
        assert sha(here / receipt['source']) == receipt['sha256']
        if not item['lean_launched']:
            assert item['kind'] == 'infrastructure'
            assert not (here / (stem + '.limits.json')).exists()
            assert log_path.read_text() == 'Failed to connect to bus: Operation not permitted\n'
            continue
        assert item['kind'] == 'lean'
        assert receipt['command'][0].endswith('/leanprover--lean4---v4.34.1/bin/lean')
        assert receipt['command'][1] == '-Dlinter.all=true'
        assert receipt['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
        assert read(here / receipt['limits']) == {
            'memory.max': '4294967296', 'memory.high': '4294967296', 'memory.swap.max': '0'}
        usage = read(here / (stem + '.usage.json'))
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        start = instant(receipt['started_at'])
        assert 0 <= (start - instant(usage['observed_at'])).total_seconds() < 120
        assert 0 <= (instant(receipt['observed_at']) - start).total_seconds() < 300
    assert (here / (PREFIX + 'direct-3.log')).stat().st_size == 0
    assert (here / (PREFIX + 'direct-3.source.lean')).read_bytes() == source.read_bytes()
    old = (here / (PREFIX + 'direct-2.source.lean')).read_text()
    assert old.replace('(scoped :', '(scopedCache :').replace('before good scoped semantic', 'before good scopedCache semantic') == source.read_text()
    printer = (here / (PREFIX + 'public-1.source.lean')).read_text()
    assert printer == (here / (PREFIX + 'public.lean')).read_text() and printer.startswith(source.read_text())
    for option in ['pp.explicit true', 'pp.fullNames true', 'pp.proofs true', 'pp.proofs.threshold 254',
                   'pp.universes true', 'pp.deepTerms true', 'pp.maxSteps 10000000', 'linter.all true']:
        assert printer.count('set_option ' + option) == 1
    log_path = here / (PREFIX + 'public-1.log')
    assert log_path.stat().st_size == selected['public_log_bytes'] == 204263
    assert sha(log_path) == selected['public_log_sha256']
    log = log_path.read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.', log)
    for head in HEADS:
        for directive in ['#check @', '#print ', '#print axioms ']:
            assert printer.count(directive + head) == 1
        checked, theorem = log.split('@' + head + ' :', 1)[1].split('\ntheorem ' + head, 1)
        declared, proof = theorem.split(' :=', 1)
        assert '_private' not in checked + declared and len(proof) > 1000
        assert ''.join(checked.split()) == ''.join(declared.removeprefix(' :').split())
        report = re.search(re.escape("'" + head + "' depends on axioms:") + r'\s*\[([^\]]*)\]', log)
        assert report is not None
        axioms = {item.strip() for item in re.sub(r'\.\{[^}]*\}', '', report.group(1)).split(',')}
        assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}
        assert sorted(axioms) == selected['axioms_by_head'][head]
    assert source.read_text().count('actual.unique (.run receipt.trace)') == 1
    assert source.read_text().count('SourceCurrentAllocatedNativeScopeCompletion.initial_complete') == 1
    print(json.dumps({'status': 'PASS', 'live': args.live, 'local_pins': len(manifest['files']),
                      'root_pins': len(pins), 'lean_jobs': 3, 'failed_checks': 1,
                      'warning_checks': 0, 'infrastructure_attempts': 1, 'canonical_jobs': 0,
                      'public_pairs': 2, 'constructed_pairs': 0,
                      'axioms_by_head': selected['axioms_by_head'],
                      'manifest_sha256': sha(here / (PREFIX + 'manifest.json'))}, indent=2))


if __name__ == '__main__':
    main()
