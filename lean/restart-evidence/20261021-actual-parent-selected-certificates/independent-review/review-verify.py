#!/usr/bin/env python3
"""Verify the selected Parent certificate review without running Lean."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

SHA='0f42191fdba120681d238bc40fcde22176ff3c2ab1bebd9ff7d179f971eca732'
HEAD='MicroCFTA.SourceCurrentActualParentSelectedCertificates.selected_certificates'
OWNER_SHA='25992d3e88952426676b785ae5588522991b5e07526a3512ae788275ce334c47'


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path) -> dict:
    return json.loads(path.read_text())


def relative(value: str) -> Path:
    path=Path(value)
    assert not path.is_absolute() and '..' not in path.parts
    return path


def check(path: Path, pin: dict) -> None:
    assert path.is_file() and path.stat().st_size==pin['bytes'] and sha(path)==pin['sha256'],str(path)


def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',required=True,type=Path)
    parser.add_argument('--live',action='store_true')
    args=parser.parse_args()
    here=Path(__file__).resolve().parent
    manifest=read(here/'review-manifest.json')
    assert manifest['finalized']
    for pin in manifest['files']:
        check(here/relative(pin['path']),pin)
    pins=read(here/'review-source-pins.json')['files']
    assert pins==manifest['sources']
    for pin in pins:
        check(here/'inputs/root'/relative(pin['path']),pin)
        if args.live:
            check(args.root/relative(pin['path']),pin)
    selected=read(here/'review-selection.json')
    assert selected['finalized'] and selected['subject']==HEAD and selected['source_sha256']==SHA
    assert selected['new_lean_commands']==selected['new_lake_commands']==selected['new_canonical_commands']==0
    assert selected['owned_public_pairs']==selected['constructed_pairs']==0
    assert selected['authored_foundations_disclosed'] and not selected['official_edits'] and not selected['material_open_findings']
    assert selected['authored_direct_dependencies']==['MicroCFTA.SourceCurrentActualParentScanNativeStores']
    assert len(selected['resolved_prelaunch_findings'])==1 and selected['resolved_prelaunch_findings'][0]['lean_jobs']==0
    assert selected['no_postlaunch_source_delta']
    owner=here/'inputs/owner'
    assert sha(owner/'selected-certificates-manifest.json')==OWNER_SHA==selected['owner_manifest_sha256']
    command=[sys.executable,str(owner/'selected-certificates-verify.py'),'--root',str(args.root)]
    if args.live:
        command.append('--live')
    result=json.loads(subprocess.check_output(command,text=True))
    assert result['status']=='PASS' and result['lean_jobs']==2 and result['failed_checks']==result['warning_checks']==0
    assert result['canonical_jobs']==result['constructed_pairs']==result['infrastructure_attempts']==0
    owner_selected=read(owner/'selected-certificates-selection.json')
    assert owner_selected['selected_strict']==selected['selected_strict']=='selected-certificates-direct-1'
    assert owner_selected['selected_public']==selected['selected_public']=='selected-certificates-public-1'
    source=owner/'SourceCurrentActualParentSelectedCertificates.lean'
    assert sha(source)==SHA and len(source.read_text().splitlines())==selected['source_lines']==263
    assert (here/'inputs/root/lean/MicroCFTA'/source.name).read_bytes()==source.read_bytes()
    text=source.read_text()
    assert re.findall(r'^theorem (\w+)',text,re.M)==['selected_certificates']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b',text)
    old=(owner/'selected-certificates-source-only.lean').read_text()
    assert hashlib.sha256(old.encode()).hexdigest()=='e1ea8ea5ce1e4839dd70da0527824e81c552385948a92a99ff99fc6ae976cbe6'
    expected=old.replace(
        '        actual = SourceCurrentAllocatedParentEdge.Edge.live noncontradictory',
        '        savedFourth = scanFourth ∧ HEq actual (SourceCurrentAllocatedParentEdge.Edge.live noncontradictory').replace(
        '        numeric.actual = SourceCurrentAllocatedParentEdge.Edge.live noncontradictory',
        '        savedFourth = scanFourth ∧ HEq numeric.actual (SourceCurrentAllocatedParentEdge.Edge.live noncontradictory').replace(
        '(SourceCurrentConjunctionScanClassPass.Reduction.completed trace retained requiredCall pass)) built) ∧',
        '(SourceCurrentConjunctionScanClassPass.Reduction.completed trace retained requiredCall pass)) built)) ∧').replace(
        '⟨built, rfl⟩, first, second, last','⟨built, rfl, HEq.rfl⟩, first, second, last')
    assert expected==text
    public='theorem selected_certificates'+text.split('theorem selected_certificates',1)[1].split(' := by',1)[0]+'\n'
    assert public==(owner/'selected-certificates-corrected-signature.lean.txt').read_text()
    assert 'savedFourth = scanFourth ∧ HEq numeric.actual' in public
    assert '(current :' not in public and '(ranges :' not in public
    assert text.count('SourceCurrentActualParentScanNativeStores.selected_scan formulas')==1
    assert text.count('selected_graph numeric.reads')==1
    assert 'SourceCurrentActualParentSemanticReads.parent formulas' not in text
    assert text.count('SourceCurrentScanNumeric.complete formulas')==1
    ledger=read(owner/'selected-certificates-attempt-ledger.json')['attempts']
    stems=[item['name'] for item in ledger]
    assert len(stems)==len(set(stems))==selected['copied_owner_lean_commands']==2
    assert set(stems)=={'selected-certificates-direct-1','selected-certificates-public-1'}
    assert all(item['lean_launched'] and item['exit_code']==0 for item in ledger)
    assert selected['copied_owner_failed_checks']==selected['copied_owner_warning_checks']==selected['copied_owner_infrastructure_attempts']==selected['copied_owner_canonical_commands']==0
    assert (owner/(selected['selected_strict']+'.log')).stat().st_size==0
    log_path=owner/(selected['selected_public']+'.log')
    assert log_path.stat().st_size==selected['full_log_bytes']==6419396
    assert sha(log_path)==selected['full_log_sha256']
    log=log_path.read_text()
    checked,theorem=log.split('@'+HEAD+' :',1)[1].split('\ntheorem '+HEAD,1)
    declared,proof=theorem.split(' :=',1)
    assert ''.join(checked.split())==''.join(declared.removeprefix(' :').split())
    assert '_private' not in checked+declared and len(proof)>1000
    axioms=re.search(re.escape("'"+HEAD+"' depends on axioms:")+r'\s*\[([^\]]*)\]',log)
    assert axioms
    names={part.strip() for part in re.sub(r'\.\{[^}]*\}','',axioms.group(1)).split(',')}
    assert sorted(names)==selected['axioms']==['Classical.choice','Quot.sound','propext']
    report=(here/'review.md').read_text()
    for phrase in ['zero Lean','Prelaunch index correction','complete selected records','ENTRY-indexed ranges',
                   'same numeric','Authorship','I authored the direct dependency ActualParentScanNativeStores']:
        assert phrase.lower() in report.lower(),phrase
    print(json.dumps({'status':'PASS','live':args.live,'local_pins':len(manifest['files']),'root_pins':len(pins),
                      'new_lean_commands':0,'new_lake_commands':0,'new_canonical_commands':0,
                      'reused_owner_lean_commands':2,'reused_failed_checks':0,'owned_public_pairs':0,
                      'resolved_prelaunch_type_issue':True,'axioms':selected['axioms'],
                      'manifest_sha256':sha(here/'review-manifest.json')},indent=2))


if __name__=='__main__':
    main()
