#!/usr/bin/env python3
"""Check the independent owner-pair review without running Lean."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

SHA = '3e10a892e36f1e5f981fc0acf60c86af543ad3e91bf46ce79205aad365c7a930'
HEAD = 'MicroCFTA.SourceCurrentActualOwnerPair.required_pair'
OWNER_SHA = '5315cef57efb3b2e81f286236551adf411839c6a1b339c605d21a594ca3882b1'


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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--live', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    manifest = read(here/'review-manifest.json')
    assert manifest['finalized']
    for pin in manifest['files']:
        check(here/relative(pin['path']),pin)
    pins = read(here/'review-source-pins.json')['files']
    assert pins == manifest['sources']
    for pin in pins:
        check(here/'inputs/root'/relative(pin['path']),pin)
        if args.live:
            check(args.root/relative(pin['path']),pin)
    selected = read(here/'review-selection.json')
    assert selected['finalized'] and selected['subject'] == HEAD and selected['source_sha256'] == SHA
    assert selected['new_lean_commands'] == selected['new_lake_commands'] == selected['new_canonical_commands'] == 0
    assert selected['owned_public_pairs'] == selected['constructed_pairs'] == 0
    assert selected['authored_foundations_disclosed'] and not selected['official_edits'] and not selected['material_findings']
    owner = here/'inputs/owner'
    assert sha(owner/'actual-owner-pair-manifest.json') == OWNER_SHA == selected['owner_manifest_sha256']
    command = [sys.executable,str(owner/'actual-owner-pair-verify.py'),'--root',str(args.root)]
    if args.live:
        command.append('--live')
    owner_result = json.loads(subprocess.check_output(command,text=True))
    assert owner_result['status'] == 'PASS' and owner_result['lean_jobs'] == 3 and owner_result['failed_checks'] == 1
    assert owner_result['canonical_jobs'] == owner_result['constructed_pairs'] == owner_result['infrastructure_attempts'] == 0
    owner_selection = read(owner/'actual-owner-pair-selection.json')
    assert owner_selection['selected_strict'] == selected['selected_strict'] == 'actual-owner-pair-direct-2'
    assert owner_selection['selected_public'] == selected['selected_public'] == 'actual-owner-pair-public-1'
    assert owner_selection['warning_checks'] == 0
    source = owner/'SourceCurrentActualOwnerPair.lean'
    assert sha(source) == SHA and len(source.read_text().splitlines()) == selected['source_lines'] == 189
    assert (here/'inputs/root/lean/MicroCFTA'/source.name).read_bytes() == source.read_bytes()
    assert re.findall(r'^theorem (\w+)',source.read_text(),re.M) == ['required_pair']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b',source.read_text())
    old = (owner/'actual-owner-pair-prelaunch-1.source.lean').read_text()
    renamed = old.replace('(prefix :','(precheckReceipt :').replace('prefix.classes','precheckReceipt.classes')
    failed = (owner/'actual-owner-pair-direct-1.source.lean').read_text()
    assert renamed == failed
    repaired = failed.replace('Record.paths','SourceEqualityClassOrder.Record.paths').replace(
        'change .ok (some (.contradiction : EqValue)) = .ok (some combined) at actual',
        'change (Except.ok (some (.contradiction : EqValue)) : Except String (Option EqValue)) =\n        Except.ok (some combined) at actual')
    assert repaired == source.read_text()
    ledger = read(owner/'actual-owner-pair-attempt-ledger.json')['attempts']
    stems = [item['name'] for item in ledger]
    assert len(stems) == len(set(stems)) == selected['copied_owner_lean_commands'] == 3
    assert set(stems) == {'actual-owner-pair-direct-1','actual-owner-pair-direct-2','actual-owner-pair-public-1'}
    assert sum(item['exit_code'] != 0 for item in ledger) == selected['copied_owner_failed_checks'] == 1
    remaining = [read(owner/(stem+'.usage.json'))['remaining_percent'] for stem in stems]
    assert remaining == selected['usage_remaining_percent'] == [52.0,52.0,51.0]
    assert all(read(owner/(stem+'.usage.json'))['age_seconds'] == 0 for stem in stems)
    assert selected['reported_prose_erratum']
    strict = owner/(selected['selected_strict']+'.log')
    assert strict.stat().st_size == 0
    log_path = owner/(selected['selected_public']+'.log')
    assert log_path.stat().st_size == selected['full_log_bytes'] == 409548
    assert sha(log_path) == selected['full_log_sha256']
    log = log_path.read_text()
    checked,theorem = log.split('@'+HEAD+' :',1)[1].split('\ntheorem '+HEAD,1)
    declared,proof = theorem.split(' :=',1)
    assert ''.join(checked.split()) == ''.join(declared.removeprefix(' :').split())
    assert '_private' not in checked+declared and len(proof) > 1000
    report = re.search(re.escape("'"+HEAD+"' depends on axioms:")+r'\s*\[([^\]]*)\]',log)
    assert report
    axioms = {part.strip() for part in re.sub(r'\.\{[^}]*\}','',report.group(1)).split(',')}
    assert sorted(axioms) == selected['axioms'] == ['Classical.choice','Quot.sound','propext']
    review = (here/'review.md').read_text()
    for phrase in ['No material issue','both class endpoints','same original row.children','zero Lean',
                   '52, 52, and 51','Authored foundations','does not claim an independent review']:
        assert phrase in review,phrase
    print(json.dumps({'status':'PASS','live':args.live,'local_pins':len(manifest['files']),
                      'root_pins':len(pins),'new_lean_commands':0,'new_lake_commands':0,
                      'new_canonical_commands':0,'reused_owner_lean_commands':3,'reused_failed_checks':1,
                      'owned_public_pairs':0,'axioms':selected['axioms'],
                      'usage_remaining_percent':remaining,
                      'manifest_sha256':sha(here/'review-manifest.json')},indent=2))


if __name__ == '__main__':
    main()
