#!/usr/bin/env python3
"""Verify this source audit without a proof or runtime command."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def relative(value: str) -> Path:
    path = Path(value)
    assert not path.is_absolute() and '..' not in path.parts, value
    return path

def check(path: Path, pin: dict) -> None:
    data = path.read_bytes()
    assert len(data) == pin['bytes'] and sha(data) == pin['sha256'], str(path)

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((HERE/'manifest.json').read_text())
    scope = json.loads((HERE/'scope.json').read_text())
    assert manifest['finalized'] and scope['finalized']
    for field in ('new_lean_commands','new_lake_commands','new_canonical_commands','new_runtime_commands'):
        assert scope[field] == 0
    assert not scope['official_edits'] and not scope['new_theorem']
    assert not scope['termination_counterexample'] and not scope['new_contract_proved']
    assert scope['non_top_warm_contract_may_be_false']
    for pin in manifest['files']:
        check(HERE/relative(pin['path']),pin)
    sources = json.loads((HERE/'source-pins.json').read_text())['sources']
    assert sources == manifest['sources']
    for pin in sources:
        snapshot = HERE/relative(pin['snapshot'])
        check(snapshot,pin)
        lines = snapshot.read_bytes().splitlines(keepends=True)
        for span in pin['reviewed_ranges']:
            lo,hi = span['start'],span['end']
            assert 1 <= lo <= hi <= len(lines)
            assert sha(b''.join(lines[lo-1:hi])) == span['sha256']
        if args.live:
            check(args.root/relative(pin['path']),pin)
    status = json.loads((HERE/'dispatch-status.json').read_text())
    parent = HERE/'inputs/dispatch-strict'
    source = (parent/'SourceCurrentResourceOwnerDispatch.lean').read_bytes()
    assert sha(source) == status['source_sha256']
    assert len(source.splitlines()) == status['source_lines'] == 187
    stem = status['selected_strict']
    receipt = json.loads((parent/(stem+'.json')).read_text())
    assert receipt['exit_code'] == 0 and receipt['sha256'] == sha(source)
    assert (parent/(stem+'.source.lean')).read_bytes() == source
    assert not (parent/(stem+'.log')).read_bytes()
    limits = json.loads((parent/(stem+'.limits.json')).read_text())
    assert limits == {'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
    usage = json.loads((parent/(stem+'.usage.json')).read_text())
    assert usage['remaining_percent'] > 1 and usage['age_seconds'] <= 600
    assert status['new_audit_proof_jobs'] == 0
    contract = (HERE/'next-contract.lean.txt').read_text()
    assert 'UNPROVED CONTRACT' in contract and 'theorem non_top_copy' in contract
    assert ' := by' not in contract
    report = (HERE/'report.md').read_text()
    assert 'DRAFT SOURCE AUDIT' in (HERE/'report-before-dispatch-strict.md').read_text()
    assert 'FROZEN SOURCE AUDIT' in report
    assert 'not a nontermination example' in report
    print(json.dumps({'status':'PASS','live':args.live,'finalized':True,
        'source_pins':len(sources),'reviewed_ranges':sum(len(x['reviewed_ranges']) for x in sources),
        'local_pins':len(manifest['files']),'new_lean_lake_canonical_runtime_jobs':0,
        'new_theorem':False,'termination_counterexample':False,
        'non_top_contract_unproved_and_may_be_false':True,
        'authored_foundations_disclosed':True,
        'manifest_sha256':sha((HERE/'manifest.json').read_bytes())},indent=2))

if __name__ == '__main__':
    main()
