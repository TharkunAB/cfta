#!/usr/bin/env python3
"""Verify the actual Parent Scan source and retained proof evidence."""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path

PREFIX = 'parent-scan-stores-'
SHA = 'fb94ee44471c161ec6d3c94348b07a38ee52fc3823ac28296c66334dc952e8e0'
HEAD = 'MicroCFTA.SourceCurrentActualParentScanNativeStores.selected_scan'


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def relative(value: str) -> Path:
    path = Path(value)
    assert not path.is_absolute() and '..' not in path.parts
    return path


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
    assert selected['finalized'] and selected['source_sha256'] == SHA
    assert selected['public_heads'] == [HEAD]
    assert (selected['lean_jobs'], selected['failed_checks'], selected['warning_checks'],
            selected['canonical_jobs'], selected['infrastructure_attempts']) == (2, 0, 0, 0, 0)
    assert (selected['new_public_pairs'], selected['constructed_pairs']) == (1, 0)
    source = here / relative(selected['source'])
    assert sha(source) == SHA and len(source.read_text().splitlines()) == selected['source_lines'] == 147
    assert re.findall(r'^theorem (\w+)', source.read_text(), re.M) == ['selected_scan']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b', source.read_text())
    assert sha(here / (PREFIX + 'source-only.lean')) == SHA == selected['source_only_sha256']
    marker = '/-- Initial resources derive admission and the native stores at the same selected Scan return. -/'
    proposal = (here / 'inputs/plan/proposed-signature.lean.txt').read_text()
    assert source.read_text().split(marker)[1].split('\n := by', 1)[0].strip() == proposal.split(marker)[1].strip()
    assert source.read_text().count('SourceCurrentActualParentSemanticReads.parent formulas') == 1
    assert source.read_text().count('SourceCurrentScanNativeStores.scan formulas') == 1
    if args.live:
        assert sha(args.root / 'lean/MicroCFTA' / source.name) == SHA
    ledger = read(here / (PREFIX + 'attempt-ledger.json'))['attempts']
    assert len(ledger) == sum(item['lean_launched'] for item in ledger) == 2
    assert {item['name']: item['exit_code'] for item in ledger} == selected['attempts']
    assert selected['selected_strict'] == PREFIX + 'direct-1'
    assert selected['selected_public'] == PREFIX + 'public-1'
    for item in ledger:
        stem = item['name']
        receipt_path, log_path = here / (stem+'.json'), here / (stem+'.log')
        assert sha(receipt_path) == item['receipt_sha256'] and sha(log_path) == item['log_sha256']
        receipt = read(receipt_path)
        assert item['kind'] == 'lean' and item['lean_launched'] and item['exit_code'] == receipt['exit_code'] == 0
        assert sha(here / relative(receipt['source'])) == receipt['sha256']
        assert receipt['command'][0].endswith('/leanprover--lean4---v4.34.1/bin/lean')
        assert receipt['command'][1] == '-Dlinter.all=true'
        assert receipt['wrapper'][1:5] == ['--mem', '4G', '--time', '5m']
        assert read(here / relative(receipt['limits'])) == {
            'memory.max':'4294967296', 'memory.high':'4294967296', 'memory.swap.max':'0'}
        usage = read(here / (stem+'.usage.json'))
        assert usage['age_seconds'] < 120 and usage['remaining_percent'] > 1
        start, finish = instant(receipt['started_at']), instant(receipt['observed_at'])
        assert 0 <= (start - instant(usage['observed_at'])).total_seconds() < 120
        assert 0 <= (finish - start).total_seconds() < 300
    strict = here / (selected['selected_strict']+'.log')
    assert strict.stat().st_size == 0
    assert (here / (selected['selected_strict']+'.source.lean')).read_bytes() == source.read_bytes()
    printer = (here / (selected['selected_public']+'.source.lean')).read_text()
    assert printer == (here / (PREFIX+'public.lean')).read_text() and printer.startswith(source.read_text())
    for option in ['pp.explicit true','pp.fullNames true','pp.proofs true','pp.proofs.threshold 254',
                   'pp.universes true','pp.deepTerms true','pp.maxSteps 10000000','linter.all true']:
        assert printer.count('set_option '+option) == 1
    for directive in ['#check @','#print ','#print axioms ']:
        assert printer.count(directive+HEAD) == 1
    log_path = here / (selected['selected_public']+'.log')
    assert log_path.stat().st_size == selected['public_log_bytes'] == 735805
    assert sha(log_path) == selected['public_log_sha256']
    log = log_path.read_text()
    assert not re.search(r'sorryAx|\b(?:warning|error)(?:\([^)]*\))?:|failed to pretty print|pp\.rawOnError|maximum recursion depth|maximum number of heartbeats|⋯|…|\.\.\.',log)
    checked, theorem = log.split('@'+HEAD+' :',1)[1].split('\ntheorem '+HEAD,1)
    declared, proof = theorem.split(' :=',1)
    assert '_private' not in checked+declared and len(proof) > 1000
    assert ''.join(checked.split()) == ''.join(declared.removeprefix(' :').split())
    report = re.search(re.escape("'"+HEAD+"' depends on axioms:")+r'\s*\[([^\]]*)\]',log)
    assert report
    axioms = {part.strip() for part in re.sub(r'\.\{[^}]*\}','',report.group(1)).split(',')}
    assert axioms <= {'propext','Classical.choice','Quot.sound'}
    assert sorted(axioms) == selected['axioms_by_head'][HEAD]
    print(json.dumps({'status':'PASS','live':args.live,'local_pins':len(manifest['files']),
                      'root_pins':len(pins),'lean_jobs':2,'failed_checks':0,'warning_checks':0,
                      'infrastructure_attempts':0,'canonical_jobs':0,'public_pairs':1,'constructed_pairs':0,
                      'axioms_by_head':selected['axioms_by_head'],
                      'manifest_sha256':sha(here/(PREFIX+'manifest.json'))},indent=2))


if __name__ == '__main__':
    main()
