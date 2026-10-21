#!/usr/bin/env python3
"""Verify frozen inherited-owner dispatch evidence without running Lean."""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import runpy
from pathlib import Path

HERE=Path(__file__).resolve().parent
PREFIX='resource-owner-inherited-dispatch-'
HEAD='MicroCFTA.SourceCurrentResourceOwnerInheritedDispatch.key_ne_inherited'

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path: Path) -> dict:
    return json.loads(path.read_text())

def relative(value: str) -> Path:
    path=Path(value)
    assert not path.is_absolute() and '..' not in path.parts,value
    return path

def check(path: Path,pin: dict) -> None:
    assert path.is_file() and path.stat().st_size==pin['bytes'] and sha(path)==pin['sha256'],str(path)

def main() -> None:
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--live',action='store_true')
    args=parser.parse_args()
    manifest=read(HERE/(PREFIX+'manifest.json'))
    assert manifest['finalized']
    for pin in manifest['files']:
        check(HERE/relative(pin['path']),pin)
    pins=read(HERE/(PREFIX+'source-pins.json'))['sources']
    assert pins==manifest['sources'] and len(pins)==8
    for pin in pins:
        snapshot=HERE/relative(pin['snapshot']);check(snapshot,pin)
        lines=snapshot.read_bytes().splitlines(keepends=True)
        assert len(lines)==pin['lines']
        for span in pin['reviewed_ranges']:
            lo,hi=span['start'],span['end']
            assert 1<=lo<=hi<=len(lines)
            assert hashlib.sha256(b''.join(lines[lo-1:hi])).hexdigest()==span['sha256']
        if args.live:
            check(args.root/relative(pin['path']),pin)
    selected=read(HERE/(PREFIX+'selection.json'))
    assert selected['finalized'] and selected['public_heads']==[HEAD]
    assert selected['warning_checks']==selected['infrastructure_attempts']==selected['canonical_jobs']==selected['constructed_pairs']==0
    assert selected['new_public_pairs']==1 and selected['official_edits_by_author'] is False
    source=HERE/selected['source'];text=source.read_text()
    assert sha(source)==selected['source_sha256']=='b50c9491cbd17847df0d96725ad45b9f0cce8d0dd0a900a6e053deeb835463b5'
    assert len(text.splitlines())==selected['source_lines']==188
    assert re.findall(r'^theorem (\w+)',text,re.M)==['key_ne_inherited']
    assert re.findall(r'^private theorem (\w+)',text,re.M)==['reservation']
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustCompiler)\b|_private',text)
    proposal=(HERE/'inputs/plan/proposed-signature.lean.txt').read_text()
    assert text.split('theorem key_ne_inherited\n',1)[1].split(' := by',1)[0]==proposal.split('theorem key_ne_inherited\n',1)[1].split('\nend MicroCFTA.',1)[0]
    assert selected['public_header_byte_exact_frozen_proposal'] and selected['proposal_elaborated_before_draft'] is False
    old=(HERE/'checked-top-dispatch.source.lean.txt').read_text()
    expected=old.replace('SourceCurrentResourceOwnerDispatch','SourceCurrentResourceOwnerInheritedDispatch').replace('SourceCurrentResourceOwnerProgress','SourceCurrentResourceOwnerInheritedProgress').replace('key_ne_top','key_ne_inherited').replace('{g s r e p h m c n budget fuel slot handle identity : Nat}','{g s r e p h m c n budget fuel slot handle : Nat}\n    {inherited : EqValue}').replace('(.live identity [])','inherited').replace('.live identity []','inherited').replace('laterGrowth identity descInputs.1','laterGrowth')
    assert text==expected
    assert (HERE/(PREFIX+'prelaunch-1.source.lean')).read_text()==text
    assert text.count('SourceCurrentResourceParentWriters.edge_call formulas solver')==1
    assert text.count('SourceCurrentResourceOwnerInheritedProgress.key_ne_inherited formulas solver')==1
    assert text.count('SourceCurrentOuterPrefixNativeStores.reached formulas solver')==3
    assert 'SourceCurrentOuterOwnerSelection.selected' not in text
    ledger=read(HERE/(PREFIX+'attempt-ledger.json'));attempts=ledger['attempts']
    assert ledger['actual_lean_jobs']==selected['lean_jobs']==len(attempts)
    assert ledger['failed_checks']==selected['failed_checks']==sum(item['exit_code']!=0 for item in attempts)
    assert ledger['copies_add_lean_jobs']==ledger['canonical_jobs']==0 and ledger['infrastructure_attempts']==[]
    assert {path.stem for path in HERE.glob(PREFIX+'*.json') if re.fullmatch(PREFIX+r'(?:direct|public)-\d+',path.stem)}=={item['name'] for item in attempts}
    for item in attempts:
        stem=item['name'];receipt=read(HERE/(stem+'.json'));log=(HERE/(stem+'.log')).read_text()
        assert item['lean_launched'] and receipt['exit_code']==item['exit_code']
        assert sha(HERE/(stem+'.json'))==item['receipt_sha256']
        assert sha(HERE/(stem+'.log'))==item['log_sha256']
        assert sha(HERE/receipt['source'])==receipt['sha256']==item['source_sha256']
        assert read(HERE/(stem+'.limits.json'))=={'memory.max':'4294967296','memory.high':'4294967296','memory.swap.max':'0'}
        usage=read(HERE/(stem+'.usage.json'))
        assert 0<=usage['age_seconds']<120 and usage['remaining_percent']>1
        assert usage['remaining_percent']==item['usage_remaining_percent']
        assert receipt['wrapper'][1:5]==['--mem','4G','--time','5m']
        assert receipt['command'][0].endswith('lean4---v4.34.1/bin/lean') and receipt['command'][1]=='-Dlinter.all=true'
        assert not re.search(r'\bwarning(?:\([^)]*\))?:',log)
    strict,public=selected['selected_strict'],selected['selected_public']
    assert read(HERE/(strict+'.json'))['exit_code']==read(HERE/(public+'.json'))['exit_code']==0
    assert not (HERE/(strict+'.log')).read_bytes()
    assert (HERE/(strict+'.source.lean')).read_bytes()==source.read_bytes()
    result=runpy.run_path(str(HERE/(PREFIX+'readback.py')))['check'](source,HERE/(public+'.source.lean'),HERE/(public+'.log'))
    assert result==read(HERE/(PREFIX+'readback.json'))
    assert result['public_log_bytes']==selected['public_log_bytes'] and result['public_log_sha256']==selected['public_log_sha256']
    assert result['axioms_by_head']==selected['axioms_by_head']
    print(json.dumps(dict(status='PASS',live=args.live,local_pins=len(manifest['files']),root_pins=len(pins),lean_jobs=selected['lean_jobs'],failed_checks=selected['failed_checks'],warning_checks=0,canonical_jobs=0,infrastructure_attempts=0,constructed_pairs=0,new_public_pairs=1,public_heads=[HEAD],all_eight_settings=True,public_type_identity=True,standard_axioms_only=True,manifest_sha256=sha(HERE/(PREFIX+'manifest.json'))),indent=2))

if __name__=='__main__':
    main()
